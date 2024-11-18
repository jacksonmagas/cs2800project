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
    const std::mutex writing_mtx;
    size_t buffsize;
    size_t num_buffs;
    
    //which buffer the write worker is writing to file write next when it fills
    size_t file_write_idx;
    
    //which buffer will be filled next with data
    size_t buffer_write_idx;
    
    //how much of the current buffer is written
    size_t buffer_byte_idx;
    
    //mutex for each division of the ring buffer to be held when reading/writing
    const std::vector<std::mutex> mtxs;
    const std::ofstream outfile;
    const std::unique_ptr<std::byte[]> buffer;
    const std::thread write_thread;
    
    //writes full buffers to outfile in second thread
    void write_worker();
public:
    ThreadedFileWriter(std::filesystem::path path, size_t buffsize, size_t num_buffs);
    ~ThreadedFileWriter();
    
    void write(std::byte* source, size_t num_bytes);
};
