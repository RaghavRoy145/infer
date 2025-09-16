#include <stdlib.h>

void set(int *y, int v) {
  //  [y |→ Y ∗ v |→ V ∗ (Y |→ W) ∧ (W = nil)]
  int *z;
  //  [y |→ Y ∗ v |→ V ∗ z |→ Z ∗ (Y |→ W) ∧ Z = nil ∧ (W = nil)]
  z = y;
  //  [ok: y |→ Y ∗ v |→ V ∗ z |→ W ∗ Y |→ W ∧ Z = nil ∧ (W = nil)]
  *z = v; // <- NPE ERROR BECAUSE OF THIS 
  //  [er: y |→ Y ∗ v |→ V ∗ z |→ W ∗ Y |→ W ∧ Z = nil ∧ W = nil]
}

void main() {
  //  [emp ∧ true]
  int *x;
  //  [x |→ X ∧ X =nil]
  x = malloc(sizeof(int*));
  if(x) {
  // [ok: ∃L. x |→ L ∗ L |→ V ∧ X = nil ∧ L != nil]
    *x = 0;
  //  [ok: ∃L. x |→ L ∗ L |→ nil ∧ X = nil ∧ L != nil]
  }
  set(x, 1);
  //  [er: ∃L. x |→ L ∗ L |→ nil ∧ X = nil ∧ L != nil] <- NPE ERROR HERE
}

