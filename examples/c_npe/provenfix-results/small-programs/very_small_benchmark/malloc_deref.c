#include <stdlib.h>

int main() {
    int *x = (int*) malloc(sizeof(int));
    if (x != NULL) *x = 42;
    free(x);
    return 0;
}
