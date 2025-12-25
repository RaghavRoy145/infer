#include <stdlib.h>
#include <stdio.h>

// Scenario 4 (CLUSTERED SKIP): The bug is latent here.
// The pointer is non-local. Crucially, its aliases are dereferenced in two
// separate, non-nested `if` blocks. This forces the tool to find two
// distinct LCAs, resulting in two minimal guards instead of one large one.
//void trigger_clustered_skip_repair(int *p_cluster) {
//    p_cluster = 0;
//    int *alias1 = p_cluster;
//    int *alias2 = p_cluster;
//    int condition1 = 1;
//    int condition2 = 1;

    // Cluster 1: The LCA for these two dereferences is this `if` block.
//    if (condition1) {
//        *alias1 = 100;
//        *p_cluster = 101;
//    }

//    printf("... some other logic happens between the clusters ...\n");

    // Cluster 2: The LCA for this dereference is this second, separate `if` block.
//    if (condition2) {
//        *alias2 = 200;
//    }
//}

// Scenario 3 (EVADE): The bug is latent here.
// Pointer is non-local, usage is at the function entry, making the start node the LCA.
//void trigger_evade_repair(int *p_evade) {
//    p_evade = 0;
//    *p_evade = 30;
//    printf("Evade scenario executed.\n");
//}

// Scenario 2 (SKIP): The bug is latent here.
// Pointer is non-local, usage is nested, so LCA is not the start node.
void trigger_skip_repair(int *p_skip) {
    p_skip = 0;
    int* p_skip_alias = p_skip;
    int x =1 ;
    if (x > 0) {
        *p_skip = 20;
    }
    *p_skip_alias = 10;
    int* p_skip_alias2 = p_skip_alias;
    printf("possible break");
    printf("possible break");
    if (p_skip_alias2 == NULL){ 
      if(1){
        *p_skip_alias2 = 3;
      }
    }
    printf("possible break");
}

// Scenario 1 (REPLACE): The bug is manifest here.
// Pointer is provably local.
//void trigger_replace_repair() {
//    int *p_local = NULL;
//    printf("Replace scenario executed.\n");
//    *p_local = 10;
//}

int main() {
  return 0;
}
