#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/*
 * Returns a heap‐allocated greeting if flag is nonzero,
 * otherwise returns NULL.
 */
char* get_message(int flag) {
    if (flag) {
        return strdup("Hello, world!");
    } else {
        return NULL;
    }
}

int main(int argc, char *argv[]) {
    /*
     * If you run with the argument "ok", flag = 1 ⇒ safe path.
     * Otherwise flag = 0 ⇒ get_message returns NULL and we crash.
     */
    int flag = (argc > 1 && strcmp(argv[1], "ok") == 0);
    char *msg = get_message(flag);

    /*
     * Null-pointer deref happens here when msg == NULL:
     * strlen(NULL) ⇒ segmentation fault.
     */
    printf("Message length: %zu\n", strlen(msg));
    printf("Message: %s\n", msg);

    free(msg);  /* safe when msg was non-NULL; undefined if msg==NULL */
    return 0;
}
