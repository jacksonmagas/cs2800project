;$ACL2s-SMode$;ACL2s
#|
Model assumptions:
64 bit system

General terminology:
write thread: the main thread which writes data into the buffer
read thread: the secondary thread which reads data from the buffer and writes to the file

Valid state:
no writes outside of allowed memory
at least one thread can proceed
all data from the write history is in memory or in the output file
  specifically the outfile is some slice of the history, and the outfile plus some amount of
  memory starting from file-write-idx is equal to the history

The program is correct if the constructor produces valid state, every step with valid input produces valid state,
and at the end of the destructor it is valid state.
At the end of the destructor the outfile also needs to exactly match the history of inputs.
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
                        ;; file is open or closed and has contents
                        (outfile . (list bool (listof bit)))
                        ;; ignoring unique ptr and memory management
                        ;; representing buffer as start and end location and a memory alist
                        ;; this will be used to check if data has been written outside the buffer
                        (buffer-start . nat)
                        (beffer-end . nat)
                        (memory . (alistof bit))
                        (write-thread . (or nil thread))
                        (read-thread . (or nil thread))))
  (local-state (oneof write-worker
                      write
                      constructor
                      destructor))
  ;; write worker has no local state for now
  (write-worker nil)
  (write (record (source-ptr . nat)
                 (source-bytes . (listof bytes))
                 (num-bytes . size-t)
                 (bytes-left . (or nil size-t))
                 (write-size . (or nil size-t))
                 (dest-ptr . (or nil nat))
                 (prev . size-t)))
  (constructor (record (buffsize . size-t)
                       (num-buffs . size-t)))
  (destructor (record (current-section-start-ptr . nat)
                      (current-section-end-ptr . nat))))

(defdata write-list (listof (listof byte)))

(definec is-valid-state (state :global-state history :write-list) :bool
  (and (is-valid-buffer state history)
       ;; this relies on having the state transitions
       ;; (! (is-deadlocked state history))
       (does-data-match state history)))