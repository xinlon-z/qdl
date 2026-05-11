// SPDX-License-Identifier: BSD-3-Clause
/*
 * Copyright (c) 2025, Linaro Ltd.
 * All rights reserved.
 */
#define _GNU_SOURCE
#define _FILE_OFFSET_BITS 64
#include <sys/ioctl.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <errno.h>
#include <fcntl.h>
#include <getopt.h>
#include <inttypes.h>
#include <pthread.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#include <linux/fs.h>
#include <libxml/parser.h>
#include <libxml/tree.h>

#include "firehose.h"
#include "file.h"
#include "list.h"
#include "patch.h"
#include "program.h"
#include "qdl.h"
#include "sparse.h"

bool qdl_debug;

#define WRITER_CHUNK_SIZE ((size_t)(1024 * 1024))

struct firehose_op *firehose_alloc_op(int type)
{
	struct firehose_op *op;

	op = calloc(1, sizeof(*op));
	if (!op)
		return NULL;

	op->type = type;
	return op;
}

void firehose_free_ops(struct list_head *ops)
{
	struct firehose_op *next;
	struct firehose_op *op;

	list_for_each_entry_safe(op, next, ops, node) {
		list_del(&op->node);
		qdl_zip_put(op->zip);
		free((void *)op->filename);
		free((void *)op->label);
		free((void *)op->start_sector);
		free((void *)op->gpt_partition);
		free((void *)op->value);
		free((void *)op->what);
		free(op);
	}
}

/*
 * Evaluate a Firehose expression: either a plain integer (decimal or hex) or
 * "NUM_DISK_SECTORS[+-N][.]".  Returns the evaluated value; sets *err to
 * -EINVAL and returns 0 on parse failure.
 */
static uint64_t evaluate_expr(const char *expr, uint64_t num_disk_sectors,
			       int *err)
{
	const char *p;
	uint64_t val;
	char *end;

	if (!strncmp(expr, "NUM_DISK_SECTORS", 16)) {
		p = expr + 16;
		val = num_disk_sectors;
		if (*p == '+')
			val += strtoull(p + 1, NULL, 0);
		else if (*p == '-')
			val -= strtoull(p + 1, NULL, 0);
		else if (*p != '\0' && *p != '.')
			goto err;
		return val;
	}

	val = strtoull(expr, &end, 0);
	if (end == expr)
		goto err;
	return val;

err:
	ux_err("failed to evaluate expression \"%s\"\n", expr);
	*err = -EINVAL;
	return 0;
}

/* CRC32 using the standard reflected polynomial 0xEDB88320 (ISO 3309 / GPT). */
static uint32_t crc32(const void *data, size_t len)
{
	const uint8_t *p = data;
	uint32_t crc = 0xffffffff;
	size_t i;
	int j;

	for (i = 0; i < len; i++) {
		crc ^= p[i];
		for (j = 0; j < 8; j++)
			crc = (crc >> 1) ^ (0xEDB88320u & -(crc & 1));
	}
	return crc ^ 0xffffffff;
}

/*
 * Evaluate "CRC32(sector_expr, size)" by reading 'size' bytes from the device
 * at the given sector and computing their CRC32.  Returns true on success.
 */
static bool eval_crc32(const char *expr, int fd, unsigned int sector_size,
		       uint64_t num_disk_sectors, uint32_t *result)
{
	char sector_expr[64];
	const char *comma;
	uint64_t sector;
	size_t expr_len;
	unsigned long sz;
	uint8_t *buf;
	ssize_t n;
	int err = 0;

	/* Expect "CRC32(sector_expr,size)" */
	if (strncmp(expr, "CRC32(", 6))
		return false;

	comma = strchr(expr + 6, ',');
	if (!comma)
		return false;

	expr_len = comma - (expr + 6);
	if (expr_len >= sizeof(sector_expr))
		return false;

	memcpy(sector_expr, expr + 6, expr_len);
	sector_expr[expr_len] = '\0';

	sector = evaluate_expr(sector_expr, num_disk_sectors, &err);
	if (err)
		return false;

	sz = strtoul(comma + 1, NULL, 0);
	if (!sz)
		return false;

	buf = malloc(sz);
	if (!buf)
		return false;

	n = pread(fd, buf, sz, (off_t)(sector * sector_size));
	if (n < 0 || (size_t)n != sz) {
		ux_err("failed to read sector %llu for CRC32: %s\n",
		       (unsigned long long)sector, strerror(errno));
		free(buf);
		return false;
	}

	*result = crc32(buf, sz);
	free(buf);
	return true;
}

static int writer_program(int fd, struct firehose_op *op,
			  unsigned int sector_size, uint64_t num_disk_sectors,
			  uint64_t *written_out)
{
	struct qdl_file file;
	uint64_t start_sector;
	uint64_t num_sectors;
	uint32_t fill_value;
	uint8_t *buf;
	uint64_t left;
	ssize_t n;
	int err = 0;
	int ret;

	if (!op->filename)
		return 0;

	start_sector = evaluate_expr(op->start_sector, num_disk_sectors, &err);
	if (err)
		return err;

	ret = qdl_file_open(op->zip, op->filename, &file);
	if (ret < 0) {
		ux_err("unable to open %s\n", op->filename);
		return -1;
	}

	if (!op->sparse) {
		num_sectors = (qdl_file_getsize(&file) + sector_size - 1) /
			      sector_size;
		if (op->num_sectors && num_sectors > op->num_sectors) {
			ux_info("%s truncated to %u sectors\n",
				op->filename, op->num_sectors);
			num_sectors = op->num_sectors;
		}
	} else {
		num_sectors = op->num_sectors;
	}

	buf = malloc(WRITER_CHUNK_SIZE);
	if (!buf) {
		ux_err("failed to allocate buffer\n");
		ret = -ENOMEM;
		goto out_close;
	}

	if (!op->sparse) {
		qdl_file_seek(&file,
			      (off_t)op->file_offset * sector_size, SEEK_SET);
	} else if (op->sparse_chunk_type == CHUNK_TYPE_FILL) {
		fill_value = op->sparse_fill_value;
		for (size_t i = 0; i + sizeof(fill_value) <= WRITER_CHUNK_SIZE;
		     i += sizeof(fill_value))
			memcpy(buf + i, &fill_value, sizeof(fill_value));
	} else if (op->sparse_chunk_type == CHUNK_TYPE_RAW) {
		qdl_file_seek(&file, op->sparse_offset, SEEK_SET);
	} else {
		ux_err("[SPARSE] unknown chunk type %u\n", op->sparse_chunk_type);
		ret = -EINVAL;
		goto out_free;
	}

	if (lseek(fd, (off_t)(start_sector * sector_size), SEEK_SET) < 0) {
		ux_err("failed to seek device to sector %llu: %s\n",
		       (unsigned long long)start_sector, strerror(errno));
		ret = -errno;
		goto out_free;
	}

	for (left = num_sectors; left > 0;) {
		size_t sectors_this = MIN(WRITER_CHUNK_SIZE / sector_size,
					  (size_t)left);
		size_t bytes_this = sectors_this * sector_size;

		if (!op->sparse ||
		    op->sparse_chunk_type != CHUNK_TYPE_FILL) {
			n = qdl_file_read(&file, buf, bytes_this);
			if (n < 0) {
				ux_err("failed to read %s\n", op->filename);
				ret = -1;
				goto out_free;
			}
			if ((size_t)n < bytes_this)
				memset(buf + n, 0, bytes_this - n);
		}

		n = write(fd, buf, bytes_this);
		if (n < 0 || (size_t)n != bytes_this) {
			ux_err("failed to write to device: %s\n",
			       strerror(errno));
			ret = -1;
			goto out_free;
		}

		left -= sectors_this;
		*written_out += bytes_this;
		ux_progress("%s", num_sectors - left, num_sectors,
			    op->label ? op->label : op->filename);
	}

	ux_info("flashed \"%s\" successfully\n",
		op->label ? op->label : op->filename);
	ret = 0;

out_free:
	free(buf);
out_close:
	qdl_file_close(&file);
	return ret;
}

static int writer_erase(int fd, struct firehose_op *op,
			unsigned int sector_size, uint64_t num_disk_sectors,
			uint64_t *written_out)
{
	uint64_t start_sector;
	size_t total_bytes;
	size_t written = 0;
	uint8_t *buf;
	ssize_t n;
	int err = 0;

	start_sector = evaluate_expr(op->start_sector, num_disk_sectors, &err);
	if (err)
		return err;

	total_bytes = (size_t)op->num_sectors * sector_size;

	buf = calloc(1, WRITER_CHUNK_SIZE);
	if (!buf) {
		ux_err("failed to allocate erase buffer\n");
		return -ENOMEM;
	}

	if (lseek(fd, (off_t)(start_sector * sector_size), SEEK_SET) < 0) {
		ux_err("failed to seek device to sector %llu: %s\n",
		       (unsigned long long)start_sector, strerror(errno));
		free(buf);
		return -errno;
	}

	while (written < total_bytes) {
		size_t chunk = MIN(WRITER_CHUNK_SIZE, total_bytes - written);

		n = write(fd, buf, chunk);
		if (n < 0 || (size_t)n != chunk) {
			ux_err("failed to erase device at sector %llu: %s\n",
			       (unsigned long long)start_sector,
			       strerror(errno));
			free(buf);
			return -1;
		}
		written += chunk;
	}

	*written_out += total_bytes;

	ux_info("erased %llu+%u\n", (unsigned long long)start_sector,
		op->num_sectors);

	free(buf);
	return 0;
}

static int writer_patch(int fd, struct firehose_op *op,
			unsigned int sector_size, uint64_t num_disk_sectors)
{
	uint64_t start_sector;
	uint64_t value;
	uint32_t crc;
	off_t byte_pos;
	uint8_t buf[8];
	unsigned int i;
	ssize_t n;
	int err = 0;

	if (!op->filename || strcmp(op->filename, "DISK"))
		return 0;

	if (!op->size_in_bytes || op->size_in_bytes > sizeof(buf)) {
		ux_err("patch size_in_bytes=%u not supported\n",
		       op->size_in_bytes);
		return -EINVAL;
	}

	start_sector = evaluate_expr(op->start_sector, num_disk_sectors, &err);
	if (err)
		return err;

	if (eval_crc32(op->value, fd, sector_size, num_disk_sectors, &crc)) {
		value = crc;
	} else {
		value = evaluate_expr(op->value, num_disk_sectors, &err);
		if (err)
			return err;
	}

	byte_pos = (off_t)(start_sector * sector_size) + op->byte_offset;

	for (i = 0; i < op->size_in_bytes; i++)
		buf[i] = (value >> (i * 8)) & 0xff;

	n = pwrite(fd, buf, op->size_in_bytes, byte_pos);
	if (n < 0 || (size_t)n != op->size_in_bytes) {
		ux_err("failed to apply patch at sector %llu+%u: %s\n",
		       (unsigned long long)start_sector, op->byte_offset,
		       strerror(errno));
		return -1;
	}

	ux_debug("applied patch \"%s\"\n", op->what ? op->what : "");
	return 0;
}

static int writer_run(int fd, struct list_head *ops, uint64_t device_size,
		      unsigned int default_sector_size, uint64_t *written_out)
{
	unsigned int patch_count = 0;
	unsigned int patch_idx = 0;
	uint64_t num_disk_sectors;
	struct firehose_op *op;
	unsigned int sec_size;
	int ret;

	list_for_each_entry(op, ops, node) {
		if (op->type == FIREHOSE_OP_PATCH && op->filename &&
		    !strcmp(op->filename, "DISK"))
			patch_count++;
	}

	list_for_each_entry(op, ops, node) {
		if (op->partition != 0) {
			ux_info("skipping operation on physical partition %d\n",
				op->partition);
			continue;
		}

		sec_size = op->sector_size ? op->sector_size : default_sector_size;
		num_disk_sectors = sec_size ? device_size / sec_size : 0;

		switch (op->type) {
		case FIREHOSE_OP_CONFIGURE:
			break;
		case FIREHOSE_OP_PROGRAM:
			ret = writer_program(fd, op, sec_size, num_disk_sectors,
					     written_out);
			if (ret)
				return ret;
			break;
		case FIREHOSE_OP_ERASE:
			ret = writer_erase(fd, op, sec_size, num_disk_sectors,
					   written_out);
			if (ret)
				return ret;
			break;
		case FIREHOSE_OP_PATCH:
			ret = writer_patch(fd, op, sec_size, num_disk_sectors);
			if (ret)
				return ret;
			if (op->filename && !strcmp(op->filename, "DISK"))
				ux_progress("Applying patches", ++patch_idx,
					    patch_count ? patch_count : 1);
			break;
		case FIREHOSE_OP_READ:
		case FIREHOSE_OP_SET_BOOTABLE:
			ux_debug("skipping unsupported op type %d\n", op->type);
			break;
		default:
			ux_err("unknown operation type %d\n", op->type);
			return -EINVAL;
		}
	}

	if (patch_count)
		ux_info("%u patches applied\n", patch_idx);

	return 0;
}

/* Read the "sectors written" field (field 7) from /sys/block/<dev>/stat. */
static uint64_t read_sectors_written(const char *devname)
{
	char path[64];
	uint64_t sectors = 0;
	FILE *f;

	snprintf(path, sizeof(path), "/sys/block/%s/stat", devname);
	f = fopen(path, "r");
	if (!f)
		return 0;
	if (fscanf(f, "%*u %*u %*u %*u %*u %*u %" SCNu64, &sectors) != 1)
		sectors = 0;
	fclose(f);
	return sectors;
}

struct sync_ctx {
	int fd;
	int result;
};

static void *fsync_thread(void *arg)
{
	struct sync_ctx *ctx = arg;

	ctx->result = fsync(ctx->fd);
	return NULL;
}

static int sync_with_progress(int fd, const char *device,
			       uint64_t written_bytes, unsigned int sector_size)
{
	struct timespec ts = { .tv_nsec = 200000000 }; /* 200 ms poll */
	struct sync_ctx ctx = { .fd = fd };
	uint64_t sectors_before, sectors_cur, flushed;
	uint64_t to_flush;
	const char *devname;
	pthread_t thread;
	int done;

	devname = strrchr(device, '/');
	devname = devname ? devname + 1 : device;

	sectors_before = read_sectors_written(devname);
	to_flush = written_bytes / sector_size;
	if (!to_flush)
		to_flush = 1;

	if (pthread_create(&thread, NULL, fsync_thread, &ctx)) {
		ux_info("syncing...\n");
		ctx.result = fsync(fd);
		ux_info("done\n");
		return ctx.result ? -1 : 0;
	}

	do {
		done = (pthread_tryjoin_np(thread, NULL) == 0);
		sectors_cur = read_sectors_written(devname);
		flushed = sectors_cur > sectors_before ?
			  sectors_cur - sectors_before : 0;
		ux_progress("Syncing", MIN(flushed, to_flush), to_flush);
		if (!done)
			nanosleep(&ts, NULL);
	} while (!done);

	ux_info("sync done\n");
	return ctx.result ? -1 : 0;
}

static void usage(FILE *out)
{
	fprintf(out,
		"usage: qdl-writer [options] rawprogram*.xml patch*.xml /dev/DEVICE\n"
		"\n"
		"Options:\n"
		"  -d, --debug             print debug messages\n"
		"  -f, --allow-missing     skip missing image files\n"
		"  -i, --include=DIR       search DIR for image files\n"
		"  -v, --version           print version and exit\n"
		"  -h, --help              print this usage info\n");
}

int main(int argc, char **argv)
{
	static const struct option options[] = {
		{ "debug",         no_argument,       0, 'd' },
		{ "allow-missing", no_argument,       0, 'f' },
		{ "include",       required_argument, 0, 'i' },
		{ "version",       no_argument,       0, 'v' },
		{ "help",          no_argument,       0, 'h' },
		{}
	};
	bool allow_missing = false;
	const char *incdir = NULL;
	struct list_head ops = LIST_INIT(ops);
	const char *device;
	uint64_t device_size;
	uint64_t written_bytes = 0;
	unsigned int sector_size;
	xmlNode *root;
	xmlDoc *doc;
	int opt;
	int fd;
	int ret;
	int i;

	ux_init();

	for (;;) {
		opt = getopt_long(argc, argv, "dfi:vh", options, NULL);
		if (opt < 0)
			break;
		switch (opt) {
		case 'd':
			qdl_debug = true;
			break;
		case 'f':
			allow_missing = true;
			break;
		case 'i':
			incdir = optarg;
			break;
		case 'v':
			print_version();
			return 0;
		case 'h':
			usage(stdout);
			return 0;
		default:
			usage(stderr);
			return 1;
		}
	}

	if (argc - optind < 2) {
		usage(stderr);
		return 1;
	}

	device = argv[argc - 1];

	fd = open(device, O_RDWR);
	if (fd < 0) {
		ux_err("failed to open %s: %s\n", device, strerror(errno));
		return 1;
	}

	if (ioctl(fd, BLKGETSIZE64, &device_size)) {
		ux_err("failed to get size of %s: %s\n", device,
		       strerror(errno));
		close(fd);
		return 1;
	}

	if (ioctl(fd, BLKSSZGET, &sector_size)) {
		ux_err("failed to get sector size of %s: %s\n", device,
		       strerror(errno));
		close(fd);
		return 1;
	}

	ux_info("device %s: %llu bytes, %u-byte sectors\n",
		device, (unsigned long long)device_size, sector_size);

	ret = 1;
	for (i = optind; i < argc - 1; i++) {
		doc = xmlReadFile(argv[i], NULL, 0);
		if (!doc) {
			ux_err("failed to parse \"%s\"\n", argv[i]);
			goto out;
		}

		root = xmlDocGetRootElement(doc);
		if (!root) {
			ux_err("empty XML file \"%s\"\n", argv[i]);
			xmlFreeDoc(doc);
			goto out;
		}

		if (!xmlStrcmp(root->name, (xmlChar *)"data"))
			ret = program_load_xml(&ops, doc, NULL, argv[i],
					       false, allow_missing, incdir);
		else if (!xmlStrcmp(root->name, (xmlChar *)"patches"))
			ret = patch_load_xml(&ops, doc, argv[i]);
		else {
			ux_err("unrecognized XML format in \"%s\"\n", argv[i]);
			xmlFreeDoc(doc);
			goto out;
		}

		xmlFreeDoc(doc);

		if (ret < 0) {
			ret = 1;
			goto out;
		}
	}

	ret = writer_run(fd, &ops, device_size, sector_size, &written_bytes);
	if (ret) {
		ret = 1;
		goto out;
	}

	if (sync_with_progress(fd, device, written_bytes, sector_size) < 0) {
		ux_err("sync failed: %s\n", strerror(errno));
		ret = 1;
	}

out:
	close(fd);
	firehose_free_ops(&ops);
	return ret;
}
