#include <stdlib.h>
#include <stdio.h>

// This is the function with the latent bug.
// It will generate a summary: "crashes if p is NULL".
void callee_might_crash(int *p) {
    *p = 123; // Latent Null Pointer Dereference
}

// This is the function where our slice logic will be tested.
// It has one safe call and one unsafe call.
void caller_with_mixed_safety(int *p_nonlocal) {
    int condition = 1;

    // This block contains a SAFE call.
    // The call to `callee_might_crash` is protected by an explicit null check.
    // The OLD logic would have incorrectly included this in the slice.
    // The NEW logic should correctly identify it as guarded and ignore it.
    if (p_nonlocal != NULL) {
        printf("Pointer is not null, safe to call.\n");
        callee_might_crash(p_nonlocal);
    }

    // Some unrelated logic to separate the two call sites.
    if (condition) {
        printf("... doing other work ...\n");
    }

    // This is the UNSAFE call.
    // There is no guard, so this is a potential bug.
    // The slice should contain ONLY this call site.
    callee_might_crash(p_nonlocal);
}

// Main makes the latent bug in `caller_with_mixed_safety` manifest.
int main(int argc, char *argv[]) {
    int *p_test = NULL;

    // This call will trigger the manifest bug report.
    // The report will be for `main`, but the analysis that matters for
    // the repair plan happens inside `caller_with_mixed_safety`.
    caller_with_mixed_safety(p_test);
    
    return 0;
}
