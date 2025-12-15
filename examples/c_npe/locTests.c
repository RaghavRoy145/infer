#include<stdlib.h>
#include<stdio.h>

// ex-1a.c
void foo1(){
 int *x = NULL;
  *x = 42;
  free(x);
}

// ex-1b.c
void foo2(){
 int *x = malloc(sizeof(int*));
  *x = 42;
  free(x);
}

// ex-1c.c
void foo3(int y){
 int *x;

 if (y> 0){
    x = NULL;
 }
 else {
    x = malloc(sizeof(int*));
    *x = 42;
 }
 free(x);
 
}

// interprocedural
void set(int *y) {
  *y = 42;
}

int main() {
  int *x = NULL;
  set(x);
  return 0;
}

// Fix Type: Assignment - to fix NPE caused by internal instantiations
//
// 1. live variable at repair with same type as defective variable
void foo4(int val) {
  int *test = NULL;
  // Fix:
  // int temp = (int){val};
  // test = &temp;

  *test = val;
}
// 2. defective variable type is third party
typedef struct ThirdParty{
  int val;
  int *hiddenField;
} ThirdParty;

void foo5(int val) {
  ThirdParty *data = malloc(sizeof(ThirdParty));
  // Fix:
  // ThirdParty temp = (ThirdParty) {val, NULL};
  // data = &test;
  data->val = val;
  data->hiddenField = NULL;
  free(data);
}

// 3. defective variable type is custom-defined type
typedef struct List {
  int val;
  struct List *next;
} List;

void foo6a(int val) {
  List *list = malloc(sizeof(List));
  // Fix:
  // List temp = (List) {val, NULL};
  // list = &temp;
  list->val = val;
  list->next = NULL;
  free(list);
}

typedef int INTNEW;

void foo6b(int val) {
  INTNEW *a = malloc(sizeof(INTNEW));
  // Fix
  // INTNEW temp = (INTNEW){val};
  // a = &temp;
  *a = val;
}
// Fix Type: Restraint - to fix NPE caused by external functions/resources
//
// 1. conditional check to constrain set of statements affected by defect variable
void foo7(int *v) {
  //Fix 
  // if(v != NULL) {
    int temp = *v;
    if(temp > 1) {
      return;
    }
    else {
      temp = 1;
    }
  // }
  return;
}

// 2. Try-catch block - NA

// Fix Type: Evade - Divert the execution of the method to avoid NPE
//
// 1. Add new Return statement in the set statements affected by the defect

void foo8(int *v) {
  //Fix 
  // if(v == NULL) {
  //   return;
  // }  
    int temp = *v;
    if(temp > 1) {
      return;
    }
    else {
      temp = 1;
    }
  return;
}

// 2. Add a new Continue statement in a loop that encounters an NPE during iteration
void foo9(int **arr) {
  int temp = 42;
  for(int i = 0; i<(sizeof(arr)/sizeof(arr[0])); i++) {
    // Fix
    // if(arr[i] == NULL) {
    //   continue;
    // }	  
    arr[i] = &temp;
  }
}


// Fix Type: Transfer - If all else fails, throw Null Pointer Exception to an external method
//
// 1. Return error() - NA ?


// Fix Type: Replacement - Change reference into a valid instance
//
// 1. Reuse - Replace using existing compatible object
//
// 1a) Global Reuse

int *t; // Global
void foo10(){
 int *x = NULL;
 // Fix
 // if(x == NULL){
 //   x = t;
 //   t = &(int){42}; 
 // }
 // remove below line
  *x = 42;
  printf("This is a test: %d\n", *x);
  free(x);
}

// 1b) Local Reuse

void foo11(){
 int *x = NULL;
 int *t; //Local
 // Fix
 // if(x == NULL){
 //   t = &(int){42}; 
 // }
 // print("This is a test: %d\n", *t);
 // remove below lines
  *x = 42;
  printf("This is a test: %d\n", *x);
  free(x);
}
// 2. Creation - Replace using newly created object
//
// 2a) Local Creation

typedef struct List1 {
  int val;
  struct List1 *next;
} List1;

void foo12(int val){
  List1 *x = malloc(sizeof(List1));
  x = NULL;
  // Fix
  // if(x == NULL) {
  //   List1 *t = &(List1){val}; 
  // }
  // printf("This is a test %d\n", t->val);
  // remove below lines
  x->val = val;
  printf("This is a test %d\n", x->val);
  free(x);
}

// 2b) Global Creation

void foo13(int val){
  List1 *x = malloc(sizeof(List1));
  x = NULL;
  // Fix
  // if(x == NULL) {
  //   List1 *x = malloc(sizeof(List1));
  //   x = &(List1){val}; 
  // }
  // printf("This is a test %d\n", x->val);
  // remove below lines
  x->val = val;
  printf("This is a test %d\n", x->val);
  free(x);
}

// Fix Type: Skipping - Skip the statement(s) where an NPE would occur - Depends on how the caller handles different Return cases
//
// 1. Line Skipping - Skip only the problematic statement

void foo14(){
  int *x = malloc(sizeof(int));
  // Fix
  // if(x != NULL){
  //   *x = 42
  // }
  // remove below line
  *x = 42;
  free(x);
}

// 2. Method Skipping - Skip the entire defective method
//
// 2a) Null - Return Null to the caller

void foo15(){
 int *x = malloc(sizeof(int*));
  // Fix
  // if(x == NULL) {
  //   return NULL
  // }
  *x = 42;
  free(x);
}

// 2b) Creation - Return new Object to the caller

int* foo16(){
  int *x = malloc(sizeof(int));
  // Fix
  // if(x == NULL){
  //   int *t = &(int){42};
  //   return t;
  // }
  *x = 42;
  return x;
}

// 2c) Reuse - Return an existing compatible object to the caller

int* foo17(){
  int *x = malloc(sizeof(int*));
  int *t = malloc(sizeof(int*));
  int i = 42;
  t = &i;
  x = NULL;
  // Fix
  // if(x == NULL){
  //   return t;
  // }
  return x;
}

// 2d) Void - Return void-method to caller

void foo18(){
  int *x = malloc(sizeof(int*));
  // Fix
  // if(x == NULL){
  //   return; 
  // }
  *x = 42;
  free(x);
}

