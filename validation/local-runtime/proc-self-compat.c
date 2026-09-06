#define _GNU_SOURCE
#include <unistd.h>
#include <dlfcn.h>
#include <stdio.h>
#include <string.h>
/* Runtime compatibility only: getpid() namespace lacks numeric proc entry,
   while /proc/self/exe is available. No proof/compiler code is modified. */
ssize_t readlink(const char *path, char *buf, size_t sz) {
  static ssize_t (*real_readlink)(const char *, char *, size_t);
  if (!real_readlink) real_readlink = dlsym(RTLD_NEXT, "readlink");
  char own[80];
  snprintf(own, sizeof own, "/proc/%d/exe", getpid());
  if (strcmp(path, own) == 0) path = "/proc/self/exe";
  return real_readlink(path, buf, sz);
}
