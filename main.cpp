#include "ThreadedFileWriter.hpp"


// tests will be for usages of the code that look like this:
int main(int argc, char** argv) {
    // buffsize and num buffs will be passed in directly in the model, file path is ignored as each writer only ever has one path
	ThreadedFileWriter writer(file_path, buffsize, num_buffs);
    writer.write(first_data, first_data_size);
    writer.write(second_data, second_data_size);
    writer.write(third_data, third_data_size);
    ...
    writer.write(last_data, last_data_size);
    // writer goes out of scope calling destructor
}

// Tests will be specified with:
// buffsize, num buffs, and lists of lists of bytes, each one being one call to write
// the expected result of tests is always that outfile contains (reverse (append first_data second_data ... last_data))
// and that all mutexes are free and the read thread is joined

// we will ignore the main function, and assume that when writer.write finishes if there is more data to write
// then write is called again, otherwise the destructor is called.