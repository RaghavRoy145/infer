#include <stdio.h>

int main() {
  int x = 42;
  int *temp;
  int *p = NULL;
  // manifests here
  printf("Keeping temp alive: %p\n", temp);
  printf("%d\n",*temp, *p);
  return 0;
}
