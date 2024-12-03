#include "pch.h"
#include "ThreadedFileWriter.hpp"
#include "logging.h"

void ThreadedFileWriter::write_worker()
{
    // changed to local as a result of modeling showing it only used here
    // the number of the buffer to try and write to file next
    size_t file_write_idx = 0;
    while (true) {
        std::unique_lock mtx(mtxs[file_write_idx], std::defer_lock);
        std::unique_lock lock(writing_mtx);
        if (writing) {
            // if we are writing then block until we are not writing
            mtx.lock();
        } else {
            // if we are not writing then we should be able to get the mtx unless we are done
            if (!mtx.try_lock()) {
                return;
            }
        }
        try {
            outfile.write(reinterpret_cast<char*>(buffer.get() + (buffsize * file_write_idx)), buffsize);
        } catch(const std::exception& e) {
            std::cerr << "Exception " << e.what() << " while writing to file.";
            return;
        }
        file_write_idx = (file_write_idx + 1) % num_buffs;
    }
}

ThreadedFileWriter::ThreadedFileWriter(std::filesystem::path path, size_t buffsize, size_t num_buffs) :
    writing(true),
    buffsize(buffsize),
    num_buffs(num_buffs),
    file_write_idx(0),
    buffer_write_idx(0),
    buffer_byte_idx(0),
    mtxs(std::vector<std::mutex>(num_buffs)),
    outfile(std::ofstream(path)),
    buffer(std::make_unique<std::byte[]>(buffsize * num_buffs))
{
    DEBUGLOG("Opening File Writer");
    mtxs[0].lock();
    write_thread = std::thread(&ThreadedFileWriter::write_worker, this);
}

ThreadedFileWriter::~ThreadedFileWriter()
{
    DEBUGLOG("Closing File Write");
    // zero out the unused memory in the last buffer
    char* current_section_start = reinterpret_cast<char*>(buffer.get()) + buffsize * (buffer_write_idx - 1);
    char* current_section_end = current_section_start + buffsize;
    std::fill(current_section_start + buffer_byte_idx, current_section_end , '\0');
    // unlock last buffer for write thread
    std::unique_lock lock(writing_mtx);
    writing = false;
    mtxs[buffer_write_idx].unlock();
    buffer_write_idx = (buffer_write_idx + 1) % num_buffs;
    mtxs[buffer_write_idx].lock();
    lock.unlock();
    //write thread finish writing to file and end thread
    if (write_thread.joinable()) {
        DEBUGLOG("Waiting for Write Thread");
        write_thread.join();
    }
    //unlock the last mutex
    mtxs[buffer_write_idx].unlock();
    DEBUGLOG("Closing File");
    outfile.close();
    DEBUGLOG("Done Closing File Writer");
}

void ThreadedFileWriter::write(std::byte* source, size_t num_bytes)
{
    while (num_bytes > 0) {
        size_t bytes_left = buffsize - buffer_byte_idx;
        size_t write_size = std::min(bytes_left, num_bytes);
        num_bytes -= write_size;
        buffer_byte_idx += write_size;
        source += write_size;
        std::byte* dest = buffer.get() + (buffsize * buffer_write_idx) + buffer_byte_idx;
        std::memcpy(dest, source, write_size);
        if (buffer_byte_idx == buffsize) {
            size_t prev = buffer_write_idx;
            buffer_write_idx = (buffer_write_idx + 1) % num_buffs;
            // lock the next one before unlocking current
            if (!mtxs[buffer_write_idx].try_lock()) {
                std::cerr << "Error: failed to aquire write buffer" << std::endl;
                mtxs[buffer_write_idx].lock();
            }
            mtxs[prev].unlock();
        }
    }
}

