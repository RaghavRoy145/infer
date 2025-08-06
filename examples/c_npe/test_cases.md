# Null Pointer Dereference Test Cases

This directory contains 20 different C programs with various null pointer dereference errors to test repair capabilities.

## Test Cases Overview

1. **test01_simple_null.c** - Direct NULL assignment and dereference
2. **test02_conditional_null.c** - Conditional path leading to null dereference
3. **test03_struct_field_null.c** - Accessing fields of NULL struct pointer
4. **test04_array_index_null.c** - Array indexing on NULL pointer
5. **test05_function_return_null.c** - Function returning NULL not checked
6. **test06_loop_null.c** - NULL dereference inside loops
7. **test07_double_pointer_null.c** - Double pointer NULL dereference
8. **test08_malloc_fail.c** - Unchecked malloc failure
9. **test09_linked_list_null.c** - NULL linked list operations
10. **test10_switch_case_null.c** - Switch case with NULL path
11. **test11_arithmetic_null.c** - Pointer arithmetic on NULL
12. **test12_string_null.c** - String operations on NULL pointer
13. **test13_callback_null.c** - NULL function pointer invocation
14. **test14_nested_struct_null.c** - Nested struct with NULL member
15. **test15_global_null.c** - Global pointer NULL dereference
16. **test16_ternary_null.c** - Ternary operator returning NULL
17. **test17_macro_null.c** - Macro hiding null dereference
18. **test18_realloc_null.c** - Unchecked realloc failure
19. **test19_union_null.c** - Union member NULL access
20. **test20_cast_null.c** - Type cast NULL dereference

## Running Tests

From the docker/repair directory:

```bash
# Test individual file
./run-repair.sh ../../examples/c_npe/test01_simple_null.c

# Test all files
for i in {01..20}; do
    echo "Testing test${i}_*.c"
    ./run-repair.sh ../../examples/c_npe/test${i}_*.c
done
```

## Expected Behavior

Each test should:
1. Be detected by Infer as having a null pointer dereference
2. Be a candidate for automated repair
3. Demonstrate different patterns of null pointer bugs

## Repair Patterns

Common repair strategies might include:
- Adding NULL checks before dereference
- Initializing pointers with valid memory
- Adding early returns on NULL conditions
- Proper error handling for allocation failures