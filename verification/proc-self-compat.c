/* Compatibility with a PID namespace whose /proc mount uses outer PID numbers.
 * Only rewrite the process's own executable link to the equivalent /proc/self/exe.
 * This does not change Lean's type checker or any proof-checking operation. */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

ssize_t readlink(const char *path, char *buf, size_t size) {
  static ssize_t (*original)(const char *, char *, size_t);
  if (!original) original = dlsym(RTLD_NEXT, "readlink");
  char own[80];
  snprintf(own, sizeof own, "/proc/%d/exe", getpid());
  return original(strcmp(path, own) == 0 ? "/proc/self/exe" : path, buf, size);
}
