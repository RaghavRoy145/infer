#include <stdlib.h>
#include <stdio.h>

void use(int *p) {
  // possible null‐deref here
  printf("%d\n", *p);
}

int main() {
  int *p = NULL;
  if (rand()%2) p = malloc(sizeof *p);
  use(p);
  return 0;
}
