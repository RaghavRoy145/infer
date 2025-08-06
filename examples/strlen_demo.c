#include <stdio.h>
#include <string.h>

// This is roughly what strlen does internally
size_t my_strlen(const char *str) {
    size_t len = 0;
    while (*str != '\0') {  // DEREFERENCES str here!
        str++;
        len++;
    }
    return len;
}

int main() {
    char *p = NULL;
    
    // Using standard strlen - Infer doesn't know it dereferences
    size_t len1 = strlen(p);  // BUG but NOT detected
    
    // Using our implementation - Infer can see the dereference
    size_t len2 = my_strlen(p);  // BUG and SHOULD be detected
    
    return 0;
}