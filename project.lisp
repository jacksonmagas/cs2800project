;$ACL2s-SMode$;ACL2s
#|
Model assumptions:
64 bit system

General terminology:
write thread: the main thread which writes data into the buffer
read thread: the secondary thread which reads data from the buffer and writes to the file
|#


(defdata size-t (range integer (0 <= _ < (expt 2 64))))
(defdata bit (range integer (0 <= _ < 2)))
(defdata byte (list bit bit bit bit))

(defdata
  ;; a thread has an id, and its local state
  (thread (record (id . nat)
                  (line-num . nat)
                  (locals . local-state)))
  ;; a mutex had an owner thread id or is free
  (mtx (oneof nat nil))
  (global-state (record (writing . bool)
                        (writing-mtx . mtx)
                        (buffsize . size-t)
                        (num-buffs . size-t)
                        (file-write-idx . size-t)
                        (buffer-byte-idx . size-t)
                        (mtxs . (listof mtx))
                        (outfile . (listof bit))
                        ;; ignoring unique ptr and memory management
                        ;; representing buffer as start and end location and a memory alist
                        ;; this will be used to check if data has been written outside the buffer
                        (buffer-start . nat)
                        (beffer-end . nat)
                        (memory . (alistof bit))
                        (write-thread . thread)
                        (read-thread . thread)))
  (local-state (oneof write-worker
                      constructor
                      destructor))
  ;; write worker has no local state for now
  (write-worker nil)
  (constructor (record (buffsize . size-t)
                       (num-buffs . size-t)))
  (destructor ))