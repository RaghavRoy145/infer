#include <stdlib.h>
#include <stdio.h>

void deep_nested_if_logic(int *ptr_a) {
    int x = 20;
    int y = 3;

    // The LCA for the ptr_a dereferences should be this outer 'if' block.
    if (x > 10) {
        int *alias_a1 = ptr_a;

        // A deeply nested structure.
        if (y < 5) {
            // First crash site for ptr_a.
            *alias_a1 = 1;
            printf("Assigned via alias_a1\n");
        }

        // A second crash site for ptr_a, outside the deepest nest.
        // This forces the LCA to be the outer 'if', not the inner one.
        *ptr_a = 2;
        printf("Assigned via ptr_a\n");
    }
}

void loop_logic(int *ptr_b) {
    // This for loop is the enclosing construct for the ptr_b dereference.
    for (int i = 0; i < 3; i++) {
        int *alias_b1 = ptr_b;
        
        // The single crash site for ptr_b.
        // The LCA for this one site should be the statement itself.
        *alias_b1 = i;
        printf("Assigned via alias_b1 in loop\n");
    }
}

void multi_alias(int *ptr_a, int *ptr_b) {
    //int *ptr_a = malloc(sizeof(int));
    //int *ptr_b = malloc(sizeof(int));

    // This condition makes the bugs manifest. On this path, both pointers become NULL.
    //if (argc > 1) {
     printf("BUG WILL BE TRIGGERED\n");
     ptr_a = NULL;
     ptr_b = NULL;
   

    // Call the two separate logic blocks. These are far apart in the CFG.

    // This for loop is the enclosing construct for the ptr_b dereference.
    for (int i = 0; i < 3; i++) {
        int *alias_b1 = ptr_b;
        *ptr_a = 1;
        // The single crash site for ptr_b.
        // The LCA for this one site should be the statement itself.
        *alias_b1 = i;
        printf("Assigned via alias_b1 in loop\n");
    }

    int x = 20;
    int y = 3;

    // The LCA for the ptr_a dereferences should be this outer 'if' block.
    if (x > 10) {
        int *alias_a1 = ptr_a;

        // A deeply nested structure.
        if (y < 5) {
            // First crash site for ptr_a.
            *alias_a1 = 1;
	    *ptr_b = 1;
            printf("Assigned via alias_a1\n");
        }

        // A second crash site for ptr_a, outside the deepest nest.
        // This forces the LCA to be the outer 'if', not the inner one.
        *ptr_a = 2;
        printf("Assigned via ptr_a\n");
    }
    free(ptr_a);
    free(ptr_b);

    }

int main(){
  return 0;
}
