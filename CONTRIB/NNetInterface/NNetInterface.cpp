#include <torch/torch.h>
#include <torch/script.h>

#include <iostream>

#include "NNetInterface.hpp"


#ifdef __cplusplus
extern "C" {
#endif
using namespace std;



torch::Tensor ArrayToTensor(Array arr) {
    // Determine the shape of the tensor
    std::vector<int64_t> shape;
    for(int i=0; i<arr.shape->len; i++){
        int dim_size = arrayGet(*(arr.shape), i).i;
        shape.push_back(dim_size);
    }

    // Get the type of the data in the array
    torch::Dtype dtype;
    switch (getDType(arr)) {
        case childType::INT:
            dtype = torch::kInt;
            break;
        case childType::FLOAT:
            dtype = torch::kFloat;
            break;
        case childType::ARRAY: {
            // If the child type is an array, recursively call ArrayToTensor for each child array
            std::vector<torch::Tensor> child_tensors;
            for (int i = 0; i < arr.len; i++) {
                Array child_arr = ((Array*)arr.data)[i];
                child_tensors.push_back(ArrayToTensor(child_arr));
            }
            // Stack the child tensors along a new dimension to create a higher-dimensional tensor
            torch::Tensor tensor = torch::stack(child_tensors);
            return tensor;
        }
        default:
            throw std::invalid_argument("Invalid child type");
    }
    
    torch::Tensor tensor = torch::from_blob(arr.data, shape, torch::TensorOptions().dtype(dtype));

    return tensor;
}


// written by ChatGPT...hopefully it isn't buggy...
Array TensorToArray(torch::Tensor tensor) {
    Array arr;
    arr.dynamic = true;
    
    // Get the data type of the tensor
    if (tensor.dtype() == torch::kInt) {
        arr.type = childType::INT;
    } else if (tensor.dtype() == torch::kFloat) {
        arr.type = childType::FLOAT;
    }
    
    // Get the size of the tensor
    int ndims = tensor.dim();
    std::vector<int64_t> shape = tensor.sizes().vec();
    
    // Allocate memory for the array
    void* data_ptr;
    if (ndims == 1) {
        // If the tensor is one-dimensional, allocate memory for a single array
        arr.len = shape[0];
        data_ptr = malloc(arr.len * sizeof(arr.type));
        std::memcpy(data_ptr, tensor.data_ptr(), arr.len * sizeof(arr.type));
    } else {
        // If the tensor is multi-dimensional, allocate memory for an array of child arrays
        arr.type = childType::ARRAY;
        arr.len = shape[0];
        data_ptr = malloc(arr.len * sizeof(Array*));
        for (int i = 0; i < arr.len; i++) {
            // Create a new child array and recursively call TensorToArray to set its values
            Array* child_arr = (Array*)malloc(sizeof(Array));
            *child_arr = TensorToArray(tensor[i]);
            ((Array**)data_ptr)[i] = child_arr;
        }
    }
    
    arr.data = data_ptr;
    return arr;
}





using torch::jit::script::Module;

Model LoadModel(char* path){
    // Allocate memory for the module pointer
    Module* module = new Module();
    if (module == NULL) {
        printf("Error allocating memory for module\n");
        return NULL;
    }

    try {
        *module = torch::jit::load(std::string(path));
        printf("Module loaded\n");
    }
    catch (const c10::Error& e) {
        std::cerr << "error loading the model\n";
        free(module); // Free the memory before returning
        return NULL;
    }

    // Cast the module pointer to void* and return it
    return (Model) module;
}




Array RunModel(Model net, Array ndarray){
    Module module = *((Module*)net);

    printf("Array to Tensor...\n");
    std::vector<torch::jit::IValue> inputs;
    torch::Tensor X = ArrayToTensor(ndarray);
    inputs.push_back(X);

    cout << "Before cout..." << endl;
    cout << inputs << endl;
    cout << "After cout..." << endl;

    cout << "Running model..." << endl;
    // Execute the model and turn its output into a tensor.
    at::Tensor output = module.forward(inputs).toTensor();

    cout << "After running the model..." << endl;
    Array out = TensorToArray(output);
    cout << "After conversion to array..." << endl;
    return out;
}

void DestroyModel(Model net){
    delete (Module*) net;
}



#ifdef __cplusplus
}
#endif