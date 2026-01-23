#include <stdlib.h>

int main() {
    int *x = (int*) malloc(sizeof(int));
    *x = 42;
    return 0;
}
