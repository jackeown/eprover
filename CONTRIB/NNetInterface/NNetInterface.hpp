#include "stdbool.h"
#include "stdio.h"
#include "stdlib.h"

#define MAX_SHAPE_SIZE 10

typedef enum {
    INT,
    FLOAT,
    ARRAY
} childType;

typedef struct array {
    void* data;
    unsigned int len;
    bool dynamic;
    childType type;
    struct array* shape; // null for shapes. (Not infinitely recursive)
} Array;

typedef union {
    int i;
    float f;
    Array a;
} ArrayEl;


// Array function declarations...
void setShape(Array* arr);
Array createArray(void* data, unsigned int len, childType type, bool dynamics);
childType getDType(Array arr);
unsigned int getNumElem(Array arr);
ArrayEl arrayGet(Array arr, unsigned int index);
ArrayEl arrayItem(Array arr);
void arraySet(Array arr, unsigned int index, ArrayEl el);

Array reshapeArray(Array arr, Array shape);

void printArrayRecursive(Array arr, unsigned int depth, bool verbose);
void printArray(Array arr);
void freeArray(Array arr);



// Array function implementations...
Array createArray(void* data, unsigned int len, childType type, bool dynamic){
    Array a;
    a.data = data;
    a.len = len;
    a.type = type;
    a.dynamic = dynamic;
    setShape(&a);
    return a;
}

childType getDType(Array arr){
    Array handle = arr;
    while(handle.type == ARRAY){
        handle = arrayGet(handle, 0).a;
    }

    return handle.type;
}

unsigned int getNumElem(Array arr){
    int prod = 1;
    for(int dim=0;dim<arr.shape->len; dim++){
        prod *= arrayGet(*(arr.shape),dim).i;
    }
    return prod;
}



ArrayEl arrayGet(Array arr, unsigned int index){
    ArrayEl ret;

    if (index >= arr.len) {
        printf("Index %d out of range for array with length %d (%p)\n", index, arr.len, arr.data);
        ret.i = -99;
        return ret;
    }

    switch(arr.type){
        case INT:
            ret.i = ((int*) arr.data)[index];
            break;
        case FLOAT:
            ret.f = ((float*) arr.data)[index];
            break;
        case ARRAY:
            ret.a = ((Array*) arr.data)[index];
            break;
    }

    return ret;
}

// Like .item() in pytorch
ArrayEl arrayItem(Array arr){
    ArrayEl ret;
    Array handle = arr;
    while (handle.type == ARRAY) {
        handle = arrayGet(handle, 0).a;
    }

    if (handle.type == INT) {
        ret.i = ((int*) handle.data)[0];
    }
    else if (handle.type == FLOAT) {
        ret.f = ((float*) handle.data)[0];
    }

    return ret;
}


void arraySet(Array arr, unsigned int index, ArrayEl el){

    if (index >= arr.len) {
        printf("Index %d out of range for array with length %d (%p)\n", index, arr.len, arr.data);
        return;
    }

    switch(arr.type){
        case INT:
            ((int*) arr.data)[index] = el.i;
            break;
        case FLOAT:
            ((float*) arr.data)[index] = el.f;
            break;
        case ARRAY:
            ((Array*) arr.data)[index] = el.a;
            break;
    }
}

// Assumes all children array always have the same length.
// i.e. nested arrays are always tensors.
void setShape(Array* arr){
    Array* shape = (Array*) malloc(sizeof(Array));

    shape->len = 0;
    shape->type = INT;
    shape->data = malloc(MAX_SHAPE_SIZE*sizeof(int));
    shape->dynamic = true;
    shape->shape = NULL; // shapes always have null shape
    Array handle = *arr;
    while(handle.type == ARRAY){
        shape->len++;
        ArrayEl el;el.i = (int) handle.len;
        arraySet(*shape, shape->len-1, el);
        handle = arrayGet(handle, 0).a;
    }

    shape->len++;
    ArrayEl el; el.i = handle.len;
    arraySet(*shape, shape->len-1, el);

    arr->shape = shape;
}



Array reshapeArray(Array arr, Array shape){
    Array result;
    result.data = NULL;
    result.len = 0;
    result.type = INT;
    result.dynamic = false;

    // childType type = getDType(arr);
    // int n = getNumElem(arr);
    // int size = (type == INT) ? sizeof(int) : sizeof(float);
    // void* data = malloc(n * size);

    // // TODO...

    // free(data);
    return result;
}








void printArrayRecursive(Array arr, unsigned int depth, bool verbose){
    if (verbose){
        printf("len: %d\n", arr.len);
        printf("childType: %s\n", arr.type == INT ? "int" : (arr.type == FLOAT ? "float" : "array")); // Geoff would hate this.
        printf("data: %p\n", arr.data);
        printf("dynamic: %s\n", arr.dynamic ? "true" : "false");
        // if (arr.shape!= NULL){
        //     printf("shape:");
        //     printArrayRecursive(*(arr.shape), depth+1, verbose);
        // }
    }

    // Print open bracket.
    for(unsigned int j = 0; j < depth; j++){
        printf("  ");
    }
    printf("[\n");

    // Base Case...
    if (arr.type == INT || arr.type == FLOAT){
        for(int i = 0; i < depth+1; i++){
            printf("  ");
        }
        for(int i=0; i < arr.len; i++){
            ArrayEl el = arrayGet(arr, i);
            if(arr.type == INT)
                printf("%d, ", el.i);
            else
                printf("%f, ", el.f);
        }
        printf("\n");
    }

    // Recursive case...
    else{
        for(unsigned int i = 0; i < arr.len; i++){
            ArrayEl el = arrayGet(arr, i);
            printArrayRecursive(el.a, depth+1, verbose);
            for(unsigned int j = 0; j < depth; j++){
                printf("  ");
            }
            printf(",\n");
        }
    }


    // Print closing bracket.
    for(unsigned int j = 0; j < depth; j++){
        printf("  ");
    }
    printf("]\n");
}

void printArray(Array arr){
    printf("%p\n", arr.data);
    printArrayRecursive(arr, 0, false);
}

void printArrayVerbose(Array arr){
    printf("%p\n", arr.data);
    printArrayRecursive(arr, 0, true);
}

void freeArray(Array arr) {
    if (arr.data != NULL) {
        if(arr.type == ARRAY){
            for(int i=0; i<arr.len; i++) {
                Array child = ((Array*) arr.data)[i];
                freeArray(child);
            }
        }

        if (arr.dynamic){
            free(arr.data);
        }
        arr.data = NULL;
    }

    if (arr.shape != NULL) {
        freeArray(*(arr.shape));
        free(arr.shape);
    }
}

// The header needs the extern "C" when being used in 
// cpp files, but not as a header for C.
#ifdef __cplusplus
extern "C" {
#endif

    typedef void* Model;
    Model LoadModel(char* path);
    Array RunModel(Model net, Array ndarray);
    void DestroyModel(Model net);

#ifdef __cplusplus
}
#endif