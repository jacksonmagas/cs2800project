;$ACL2s-SMode$;ACL2s
#|
Model assumptions:
64 bit system
write thread id = 17
read thread id = 23

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

(modeling-validate-defs)


(def-const *write-thread-id* 17)
(def-const *read-thread-id* 23)

;; this type was potentially causing crashes because very large test values were being chosen
;; (defdata size-t (range integer (0 <= _ < (expt 2 64))))
(defdata size-t nat)
(defdata local-unsigned (or nil size-t))
(definec u+ (l r :size-t) :size-t (mod (+ l r) (expt 2 64)))
(definec u- (l r :size-t) :size-t (mod (- l r) (expt 2 64)))
(definec u* (l r :size-t) :size-t (mod (* l r) (expt 2 64)))

(defdata signed (range integer ((- (expt 2 63)) <= _ < (expt 2 63))))
(defdata local-signed (or nil signed))

(defdata bit (range integer (0 <= _ < 2)))
(defdata bits (listof bit))
(defdata byte (list bit bit bit bit))
(defdata bytes (listof byte))
;; this is the list of data provided per call of (write)
(defdata write-list (listof bytes))

(defdata indexed-list (alistof nat bit))
(defdata file (list bool bits))
(defdata free 'free)
;; a mutex had an owner thread id or is free
(defdata mtx (oneof nat free))
(defdata maybe-mtx (or nil mtx))

(defdata mtx-list (listof mtx))

(set-bogus-mutual-recursion-ok :warn)
(defdata
  (local-state (oneof write-worker
                      write-fun
                      destructor))
  ;; mtx changed to nat or free so we can tell the difference between mtx not assigned, and mtx assigned but free
  (write-worker (record (local-mtx . maybe-mtx)
                        (file-write-index . local-unsigned)))
  (write-fun (record (source-ptr . local-unsigned)
                 (source-bytes . bytes)
                 (num-bytes . size-t)
                 (bytes-left . local-unsigned)
                 (write-size . local-unsigned)
                 (dest-ptr . local-unsigned)
                 (prev . local-unsigned)))
  (destructor (record (current-section-start-ptr . local-unsigned)
                      (current-section-end-ptr . local-unsigned))))

(defdata 
  ;; a thread has an id, and its local state
  thread (record (id . nat)
                 (action-num . nat)
                 (locals . local-state)))
(defdata maybe-thread (or nil thread))

(defdata
  globals (record (writing . bool)
                       (writing-mtx . mtx)
                       (buffsize . size-t)
                       (num-buffs . size-t)
                       (buffer-write-idx . size-t)
                       (buffer-byte-idx . size-t)
                       (mtxs . mtx-list)
                       ;; file is open or closed and has contents
                       (outfile . file)
                       ;; ignoring unique ptr and memory management
                       ;; representing buffer as start and end location and a memory alist
                       ;; this will be used to check if data has been written outside the buffer
                       (buffer-start . nat)
                       ;; buffer end is the pointer to the address after the end of the buffer
                       (buffer-end . nat)
                       (memory . indexed-list)
                       (write-thread . thread)
                       (read-thread . maybe-thread)
                       (pending-writes . write-list)))

(defdata error 'locking-owned-mtx)
;; the result can be a state, or a type of error
(defdata result (oneof globals error))

(definec n-of-helper (n :nat el :all res :tl) :tl
  (if (zp n) res (n-of-helper (1- n) el (cons el res))))

(definec n-of (n :nat el :all) :tl
  (rev (n-of-helper n el '())))

(property n-mtx (n :nat m :mtx)
  (mtx-listp (n-of n m)))

(definec all-size-t (w :write-list) :bool
  (v (endp w) (^ (size-tp (llen (car w))) (all-size-t (cdr w)))))


(defmacro make-read (num mtx f-w-index)
  `(thread ,*read-thread-id* ,num (write-worker ,mtx ,f-w-index)))


;; constructor is not simulated line by line, instead used to generate initial global state
;; ignoring file path argument, as that is outside the scope of the model, also adding argument to specify the writes that will be performed
(definec constructor (buffsize num-buffs :size-t pending-writes :write-list) :globals
  :ic (all-size-t pending-writes)
  ;; write-thread id = 17
  ;; read-thread id = 23
  (let ((new-mtxs (cons 17 (n-of (u- num-buffs 1) 'free)))
        ;; if there are any writes then write thread starts in write-fun, otherwise start in destructor
        (new-write-thread (thread *write-thread-id*
                                  0
                                  (if (endp pending-writes)
                                    (destructor nil nil)
                                    (write-fun 0
                                               (car pending-writes)
                                               (llen (car pending-writes))
                                               nil
                                               nil
                                               nil
                                               nil))))
        (new-read-thread (make-read 0 nil nil)))
    (globals t
             'free
             buffsize
             num-buffs
             0
             0
             new-mtxs
             '(t ())
             0
             (u* buffsize num-buffs)
             '()
             new-write-thread
             new-read-thread
             pending-writes)))#|ACL2s-ToDo-Line|#


;; update state by giving current state and a list of pairs like '(writing . nil) or '(buffsize . 5)
(defmacro update (state &rest rst)
  (declare (xargs :guard (alistp rst)))
  (let ((writing (if (assoc 'writing rst) 
                     (cdr (assoc 'writing rst)) 
                     (globals-writing state)))
        (writing-mtx (if (assoc 'writing-mtx rst) 
                         (cdr (assoc 'writing-mtx rst)) 
                         (globals-writing-mtx state)))
        (buffsize (if (assoc 'buffsize rst) 
                      (cdr (assoc 'buffsize rst)) 
                      (globals-buffsize state)))
        (num-buffs (if (assoc 'num-buffs rst) 
                       (cdr (assoc 'num-buffs rst)) 
                       (globals-num-buffs state)))
        (buffer-byte-idx (if (assoc 'buffer-byte-idx rst) 
                             (cdr (assoc 'buffer-byte-idx rst)) 
                             (globals-buffer-byte-idx state)))
        (mtxs (if (assoc 'mtxs rst) 
                  (cdr (assoc 'mtxs rst)) 
                  (globals-mtxs state)))
        (outfile (if (assoc 'outfile rst) 
                     (cdr (assoc 'outfile rst)) 
                     (globals-outfile state)))
        (buffer-start (if (assoc 'buffer-start rst) 
                          (cdr (assoc 'buffer-start rst)) 
                          (globals-buffer-start state)))
        (buffer-end (if (assoc 'buffer-end rst) 
                        (cdr (assoc 'buffer-end rst)) 
                        (globals-buffer-end state)))
        (memory (if (assoc 'memory rst) 
                    (cdr (assoc 'memory rst)) 
                    (globals-memory state)))
        (write-thread (if (assoc 'write-thread rst) 
                          (cdr (assoc 'write-thread rst)) 
                          (globals-write-thread state)))
        (read-thread (if (assoc 'read-thread rst) 
                         (cdr (assoc 'read-thread rst)) 
                         (globals-read-thread state)))
        (pending-writes (if (assoc 'read-thread rst) 
                         (cdr (assoc 'pending-writes rst)) 
                         (globals-read-thread state))))
    `(globals ,writing ,writing-mtx ,buffsize ,num-buffs ,buffer-byte-idx
                   ,mtxs ,outfile ,buffer-start ,buffer-end 
                   ,memory ,write-thread ,read-thread ,pending-writes)))

#|
void ThreadedFileWriter::write_worker()
{
0    while (true) {
         // update mtx in the local state to be the mutex from the array
         // file write index must not change while in line 1
1        std::unique_lock mtx(mtxs[file_write_idx], std::defer_lock);
         // attempt to aquire writing mtx
2        std::unique_lock lock(writing_mtx);
         // writing var can't be modified while on line 3
3        if (writing) {
4            mtx.lock();
         } else {
             // lock must not be owned by read thread when we try locking it
5            if (!mtx.try_lock()) {
                 // unlock lock
6                return;
             }
         }
         try {
             // for now assuming that write cannot fail, can possibly look at that later
7            outfile.write(reinterpret_cast<char*>(buffer.get() + (buffsize * file_write_idx)), buffsize);
         } catch(const std::exception& e) {
8            std::cerr << "Exception " << e.what() << " while writing to file.";
9            return;
         }
10       file_write_idx = (file_write_idx + 1) % num_buffs;
      }
}
|#
;; take the state and execute an action for write worker, returning the new state or an error
(definec step-write-worker (state :globals) :result
  ;; the read thread has to be in write worker
  :ic (^ (globals-read-thread state) (write-workerp (thread-locals (globals-read-thread state))))
  (let* ((thread (globals-read-thread state))
         (id (thread-id thread))
         (line-num (thread-action-num thread))
         (locals (thread-locals thread))
         (f-w-index (write-worker-file-write-index locals))
         (mtx (write-worker-local-mtx locals))
         (mtxs (globals-mtxs state))
         (writing-mtx (globals-writing-mtx state))
         (writing (globals-writing state)))
    (match line-num
      (0 (update state `(read-thread . ,(thread id 1 mtx))))
      ;; just set local mtx variable
      (1 (update state `(read-thread . ,(thread id 2 (nth f-w-index mtxs)))))
      ;; attempt to aquire writing mtx, if it is free lock it and step line num, if it is owned by another thread block,
      ;; if it is owned by this thread that is an ERROR
      (2 (if (!= writing-mtx 'free)
           (if (== writing-mtx *read-thread-id*)
             'locking-owned-mtx
             state)
           (update state `(writing-mtx . ,*read-thread-id*) `(read-thread . ,(thread id 3 mtx)))))
      ;; conditionally jump to line 4 or line 5
      (3 (if writing 
           (update state `(read-thread . ,(thread id 4 mtx)))
           (update state `(read-thread . ,(thread id 5 mtx)))))
      (4 (if (!= mtx 'free)
           (if (== mtx *read-thread-id*)
             'locking-owned-mtx
             state)
           (update state `(read-thread . ,(thread id 7 *read-thread-id*)))))
      (5 (if (!= mtx 'free)
             (if (== mtx *read-thread-id*)
               'locking-owned-mtx
               ;; we can't get the lock so just step line number
               (update state `(read-thread . ,(thread id 6 mtx))))
             ;; we can get the lock so step line number and replace mutex id
             (update state `(mtxs . ,(update-nth f-w-index *read-thread-id* mtxs))
                     `(read-thread . ,(thread id 7 *read-thread-id*)))))
      ;; return statement ends the thread since write-worker is only called from std::thread
      ;; unique_locks are unlocked
      (6 (update state `()))
      (7 )
      (10 ))))

(definec is-valid-state (state :globals history :write-list) :bool
  (and (is-valid-buffer state history)
       ;; this relies on having the state transitions
       ;; (! (is-deadlocked state history))
       (does-data-match state history)))