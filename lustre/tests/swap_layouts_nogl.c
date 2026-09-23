// SPDX-License-Identifier: GPL-2.0-only
/*
 * This file is part of Lustre, http://www.lustre.org/
 *
 * Swap the layouts of two files with no group lock and no data version
 * check, so the request reaches the MDT without the client first
 * fetching either layout.
 */

#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <lustre/lustreapi.h>

int main(int argc, char *argv[])
{
	int fd1;
	int fd2;
	int rc;

	if (argc != 3) {
		fprintf(stderr, "usage: %s file1 file2\n", argv[0]);
		exit(1);
	}

	fd1 = open(argv[1], O_WRONLY | O_LOV_DELAY_CREATE);
	if (fd1 < 0) {
		fprintf(stderr, "open '%s': %s\n", argv[1], strerror(errno));
		exit(1);
	}

	fd2 = open(argv[2], O_WRONLY | O_LOV_DELAY_CREATE);
	if (fd2 < 0) {
		fprintf(stderr, "open '%s': %s\n", argv[2], strerror(errno));
		exit(1);
	}

	rc = llapi_fswap_layouts_grouplock(fd1, fd2, 0, 0, 0, 0);
	if (rc < 0)
		fprintf(stderr, "swap '%s' '%s': %s\n", argv[1], argv[2],
			strerror(-rc));

	close(fd2);
	close(fd1);

	return rc < 0 ? 1 : 0;
}
