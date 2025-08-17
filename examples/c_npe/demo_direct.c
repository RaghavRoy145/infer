#include <stdio.h>
#include <stdlib.h>
#include <string.h>

char* get_message(int flag) {
    if (flag) {
        return strdup("Hello, world!");
    } else {
        return NULL;
    }
}

int main(int argc, char *argv[]) {
    int flag = 0;  // Force the NULL path
    char *msg = get_message(flag);
    
    // Direct dereference - this should be caught by Infer
    char first_char = *msg;
    
    printf("First char: %c\n", first_char);
    return 0;
}