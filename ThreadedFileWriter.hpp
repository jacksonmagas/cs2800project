#include <string>
#include <vector>
#include <mutex>
#include <fstream>
#include <iostream>
#include <filesystem>

// This class provides an interface for writing data to a file in another thread
// Data is provided to a ring buffer and then written to another thread
class ThreadedFileWriter {
    bool writing;
    std::mutex writing_mtx;
    const size_t buffsize;
    const size_t num_buffs;
    
    //which buffer will be filled next with data
    size_t buffer_write_idx;
    
    //how much of the current buffer is written
    size_t buffer_byte_idx;
    
    //mutex for each division of the ring buffer to be held when reading/writing
    std::vector<std::mutex> mtxs;
    std::ofstream outfile;
    std::unique_ptr<std::byte[]> buffer;
    std::thread write_thread;
    
    //writes full buffers to outfile in second thread
    void write_worker();
public:
    ThreadedFileWriter(std::filesystem::path path, size_t buffsize, size_t num_buffs);
    ~ThreadedFileWriter();
    
    void write(std::byte* source, size_t num_bytes);
};
