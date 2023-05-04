#include "NNetInterface.hpp"

int main(void){
    float inputs[5] = {1., 2., 3., 4., 5.};

    // Testing C Array Interface...
    printf("Inputs Array:\n");
    Array inputs_array = createArray(inputs, 5, FLOAT, false);
    printArrayVerbose(inputs_array);

    // Test calling a torchscript model...
    Model critic = LoadModel("./model.torchscript");
    Array output = RunModel(critic, inputs_array);
    printArray(output);

    printf("Output number: %f\n", arrayItem(output).f);

}
