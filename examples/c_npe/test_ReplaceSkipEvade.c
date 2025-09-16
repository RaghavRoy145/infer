#include <stdlib.h>

// Dummy function to make a pointer "escape" the local context.
// The analyzer can't be sure this function doesn't store the pointer globally.
void escape_function(int *p) {
    // Does nothing, but the act of passing the pointer is what matters.
    if (p != NULL) {
        // We use 'p' to avoid an "unused parameter" warning.
    }
}

// SCENARIO 1: A provably local pointer.
// EXPECTATION: is_provably_local returns true, REPLACE repair is applied.
void test_replace_success() {
    int *local_ptr = NULL;
    // The bug is here. 'local_ptr' is never reassigned, never escapes,
    // and is not a parameter. It is a perfect candidate for replacement.
    *local_ptr = 5;
}

// SCENARIO 2: A pointer that escapes the local context.
// EXPECTATION: is_provably_local returns false, falls back to SKIP repair.
void test_fallback_to_skip() {
    int *escaping_ptr = NULL;

    // By passing the pointer to another function, it "escapes".
    // Our locality check should see this and fail.
    escape_function(escaping_ptr);

    // The bug is here.
    *escaping_ptr = 10;
}

// SCENARIO 3: A bug caused by a NULL parameter on function entry.
// EXPECTATION: is_provably_local is false. The LCA of the dereference is the
//              start node, triggering the EVADE repair.
void test_evade(int *param_ptr) {
    // The bug is here. The crash is unconditional if param_ptr is NULL.
    // The LCA of this dereference is the start node of this function.
    *param_ptr = 20;
}

// Main function to call all test cases.
int main() {
    test_replace_success();

    test_fallback_to_skip();

    // Trigger the evade case by passing NULL.
    int *t = NULL;
    test_evade(t);

    return 0;
}
