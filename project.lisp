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
(acl2s-defaults :set testing-enabled nil)
(set-defunc-function-contract-strictp nil)
(set-defunc-body-contracts-strictp nil)


(def-const *write-thread-id* 17)
(def-const *read-thread-id* 23)

;; this type was potentially causing crashes because very large test values were being chosen
(defdata size-t (range integer (0 <= _ < (expt 2 64))))
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
                 (atomic-num . nat)
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

(defdata error (or 'locking-owned-mtx 'writing-to-closed-file 'memory-access-error 'unlocking-unowned-mtx))
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


;; helper for making read threads
(definec make-read (num :size-t m :maybe-mtx f-w-index :local-unsigned) :thread
  `(thread ,*read-thread-id* ,num (write-worker ,m ,f-w-index)))


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
             pending-writes))
  :skip-function-contractp t
  :skip-tests t)

;; update state by giving current state and a list of pairs like '(writing . nil) or '(buffsize . 5)
(definec update (lstate :globals rst :alist) :globals
  (let ((writing (if (assoc 'writing rst) 
                   (cdr (assoc 'writing rst)) 
                   (globals-writing lstate)))
        (writing-mtx (if (assoc 'writing-mtx rst) 
                       (cdr (assoc 'writing-mtx rst)) 
                       (globals-writing-mtx lstate)))
        (buffsize (if (assoc 'buffsize rst) 
                    (cdr (assoc 'buffsize rst)) 
                    (globals-buffsize lstate)))
        (num-buffs (if (assoc 'num-buffs rst) 
                     (cdr (assoc 'num-buffs rst)) 
                     (globals-num-buffs lstate)))
        (buffer-write-idx (if (assoc 'buffer-write-idx rst) 
                            (cdr (assoc 'buffer-write-idx rst)) 
                            (globals-buffer-byte-idx lstate)))
        (buffer-byte-idx (if (assoc 'buffer-write-idx rst) 
                           (cdr (assoc 'buffer-byte-idx rst)) 
                           (globals-buffer-byte-idx lstate)))
        (mtxs (if (assoc 'mtxs rst) 
                (cdr (assoc 'mtxs rst)) 
                (globals-mtxs lstate)))
        (outfile (if (assoc 'outfile rst) 
                   (cdr (assoc 'outfile rst)) 
                   (globals-outfile lstate)))
        (buffer-start (if (assoc 'buffer-start rst) 
                        (cdr (assoc 'buffer-start rst)) 
                        (globals-buffer-start lstate)))
        (buffer-end (if (assoc 'buffer-end rst) 
                      (cdr (assoc 'buffer-end rst)) 
                      (globals-buffer-end lstate)))
        (memory (if (assoc 'memory rst) 
                  (cdr (assoc 'memory rst)) 
                  (globals-memory lstate)))
        (write-thread (if (assoc 'write-thread rst) 
                        (cdr (assoc 'write-thread rst)) 
                        (globals-write-thread lstate)))
        (read-thread (if (assoc 'read-thread rst) 
                       (cdr (assoc 'read-thread rst)) 
                       (globals-read-thread lstate)))
        (pending-writes (if (assoc 'read-thread rst) 
                          (cdr (assoc 'pending-writes rst)) 
                          (globals-read-thread lstate))))
    (globals writing writing-mtx buffsize num-buffs buffer-write-idx
             buffer-byte-idx mtxs outfile buffer-start buffer-end 
             memory write-thread read-thread pending-writes)))

(defdata bits-error (or bits error))
;; get the memory from a buffer
(definec mem-get (mem :indexed-list start-idx end-idx :size-t) :bits-error
  (if (= start-idx end-idx)
    '()
    (if (^ (assoc start-idx mem) (! (errorp (mem-get mem (1+ start-idx) end-idx))))
      (cons (assoc start-idx mem) (mem-get mem (1+ start-idx) end-idx))
      'memory-access-error)))

#|
void ThreadedFileWriter::write_worker()
{
0    size_t file_write_idx = 0;
1    while (true) {
         // update mtx in the local state to be the mutex from the array
         // file write index must not change while in line 1
2        std::unique_lock mtx(mtxs[file_write_idx], std::defer_lock);
         // attempt to aquire writing mtx
3        std::unique_lock lock(writing_mtx);
         // writing var can't be modified while on line 3
4        if (writing) {
5            mtx.lock();
         } else {
             // lock must not be owned by read thread when we try locking it
6            if (!mtx.try_lock()) {
                 // unlock lock
7                return;
             }
         }
         try {
             // for now assuming that write cannot fail, can possibly look at that later
8            outfile.write(reinterpret_cast<char*>(buffer.get() + (buffsize * file_write_idx)), buffsize);
         } catch(const std::exception& e) {
9            std::cerr << "Exception " << e.what() << " while writing to file.";
10           return;
         }
11      file_write_idx = (file_write_idx + 1) % num_buffs;
      }
}
|#
;; take the state and execute an action for write worker, returning the new state or an error
(definec step-write-worker (prog-state :globals) :result
  ;; the read thread has to be in write worker
  :ic (^ (globals-read-thread prog-state) (write-workerp (thread-locals (globals-read-thread prog-state))))
  (let* ((thread (globals-read-thread prog-state))
         (line-num (thread-atomic-num thread))
         (locals (thread-locals thread))
         (f-w-index (write-worker-file-write-index locals))
         (mtx (write-worker-local-mtx locals))
         (mtxs (globals-mtxs prog-state))
         (writing-mtx (globals-writing-mtx prog-state))
         (writing (globals-writing prog-state))
         (file (globals-outfile prog-state))
         (mem (globals-memory prog-state))
         (buff-start (globals-buffer-start prog-state))
         (buffsize (globals-buffsize prog-state))
         (num-buffs (globals-num-buffs prog-state)))
    (match line-num
      ;; initialize file write index to 0
      (0 (update prog-state `((read-thread . ,(make-read 1 mtx 0)))))
      ;; just step line
      (1 (update prog-state `((read-thread . ,(make-read 2 mtx f-w-index)))))
       ;; set local mtx variable
      (2 (update prog-state `((read-thread . ,(make-read 3 (nth f-w-index mtxs) f-w-index)))))
       ;; attempt to aquire writing mtx, if it is free lock it and step line num, if it is owned by another thread block,
       ;; if it is owned by this thread that is an ERROR
      (3 (if (!= writing-mtx 'free)
           (if (== writing-mtx *read-thread-id*)
             'locking-owned-mtx
             prog-state)
           (update prog-state `((writing-mtx . ,*read-thread-id*) (read-thread . ,(make-read 4 mtx f-w-index))))))
      ;; conditionally jump to line 4 or line 5
      (4 (if writing 
           (update prog-state `(read-thread . ,(make-read 5 mtx f-w-index)))
           (update prog-state `(read-thread . ,(make-read 6 mtx f-w-index)))))
      ;; try to aquire mtx, error if already holding it, set mtx local variable and the global mutex, otherwise wait
      (5 (if (!= mtx 'free)
           (if (== mtx *read-thread-id*)
             'locking-owned-mtx
             prog-state)
           (update prog-state `((mtxs . ,(update-nth f-w-index *read-thread-id* mtxs))
                                (read-thread . ,(make-read 7 *read-thread-id* f-w-index))))))
      ;; same as 5 but move to next line if not holding it
      (6 (if (!= mtx 'free)
           (if (== mtx *read-thread-id*)
             'locking-owned-mtx
             ;; we can't get the lock so just step line number
             (update prog-state `((read-thread . ,(make-read 7 mtx f-w-index)))))
           ;; we can get the lock so step line number and replace mutex id
           (update prog-state `((mtxs . ,(update-nth f-w-index *read-thread-id* mtxs))
                                `(read-thread . ,(make-read 8 *read-thread-id* f-w-index))))))
      ;; return statement ends the thread since write-worker is only called from std::thread
      ;; unique_locks are unlocked
      ;; this is correct because the mutex is unlocked nowhere else
      ;; we don't need to update the local version of the mutex because the thread ended
      (7 (update prog-state `((mtxs . ,(update-nth f-w-index 'free mtxs))
                              (read-thread . nil))))
      ;; write to the file, not considering file write exceptions
      ;; ensures that whole buffer has values
      (8 (if (car file)
           (let ((buf (mem-get mem (+ buff-start (* buffsize f-w-index)) (+ buff-start (* buffsize (1+ f-w-index))))))
             (if (errorp buf)
               buf
               (update prog-state `((outfile . ,buf)
                                    (read-thread . ,(make-read 11 mtx f-w-index))))))
           'writing-to-closed-file))
      ;; update file_write_idx = (file_write_idx + 1) % num_buffs
      ;; also unlock unique_locks, mtx local var goes out of scope and becomes nil
      ;; wrap around to start of loop
      (11 (update prog-state `((mtxs . ,(update-nth f-w-index 'free mtxs))
                               (read-thread . ,(make-read 1 nil (mod (1+ f-w-index) num-buffs))))))))
      :skip-tests t)


(definec destructor-thread (line-num :size-t start-ptr end-ptr :local-unsigned) :thread
  (thread *write-thread-id* line-num (destructor start-ptr end-ptr)))

(defdata er-indexed-list (or error indexed-list))
(definec set-memory (mem :indexed-list st-ptr end-ptr :size-t val :bit) :er-indexed-list
  (if (> st-ptr end-ptr)
    'invalid-memset
    (if (= st-ptr end-ptr)
      mem
      (set-memory (put-assoc st-ptr val mem) (1+ st-ptr) end-ptr val))))

#|
ThreadedFileWriter::~ThreadedFileWriter()
{
     DEBUGLOG("Closing File Write");
     // zero out the unused memory in the last buffer
0    char* current_section_start = reinterpret_cast<char*>(buffer.get()) + buffsize * (buffer_write_idx - 1);
1    char* current_section_end = current_section_start + buffsize;
2    std::fill(current_section_start + buffer_byte_idx, current_section_end , '\0');
     // unlock last buffer for write thread
3    std::unique_lock lock(writing_mtx);
4    writing = false;
5    mtxs[buffer_write_idx].unlock();
6    buffer_write_idx = (buffer_write_idx + 1) % num_buffs;
7    mtxs[buffer_write_idx].lock();
8    lock.unlock();
     //write thread finish writing to file and end thread
     DEBUGLOG("Waiting for Write Thread");
9    write_thread.join();
     //unlock the last mutex
10   mtxs[buffer_write_idx].unlock();
     DEBUGLOG("Closing File");
11   outfile.close();
     DEBUGLOG("Done Closing File Writer");
}
(destructor (record (current-section-start-ptr . local-unsigned)
                      (current-section-end-ptr . local-unsigned))))
|#
(definec step-destructor (prog-state :globals) :result
  (let* ((thread (globals-write-thread prog-state))
         (line-num (thread-atomic-num thread))
         (locals (thread-locals thread))
         (cur-sec-start (destructor-current-section-start-ptr locals))
         (cur-sec-end (destructor-current-section-end-ptr locals))
         (buff-start (globals-buffer-start prog-state))
         (buffsize (globals-buffsize prog-state))
         (buffer-write-idx (globals-buffer-write-idx prog-state))
         (buffer-byte-idx (globals-buffer-byte-idx prog-state))
         (num-buffs (globals-num-buffs prog-state))
         (mtxs (globals-mtxs prog-state))
         (cur-mtx (nth buffer-write-idx mtxs))
         (writing-mtx (globals-writing-mtx prog-state))
         (read-thread (globals-read-thread prog-state))
         (outfile (cdr (globals-outfile prog-state)))
         (memory (globals-memory prog-state)))
    (match line-num
      ;; set current-section-start local
      (0 (update prog-state `((write-thread . ,(destructor-thread 1 (+ buff-start (* buffsize (1- buffer-write-idx))) cur-sec-end)))))
      ;; set current-section-end local
      (1 (update prog-state `((write-thread . ,(destructor-thread 2 cur-sec-start (+ cur-sec-start buffsize))))))
      ;; set the rest of the memory in the current buffer section to zero
      (2 (update prog-state `((write-thread . ,(destructor-thread 3 cur-sec-start cur-sec-end))
                              (memory . ,(set-memory memory (+ cur-sec-start buffer-byte-idx) cur-sec-end 0)))))
      ;; lock writing mutex, blocking if not free
      (3 (if (!= writing-mtx 'free)
           (if (== writing-mtx *write-thread-id*)
             'locking-owned-mtx
             prog-state)
           (update prog-state `((writing-mtx . ,*write-thread-id*)
                                (write-thread . ,(destructor-thread 4 cur-sec-start cur-sec-end))))))
      ;; set writing var to false
      (4 (update prog-state `((writing . nil)
                              (write-thread . ,(destructor-thread 5 cur-sec-start cur-sec-end)))))
      ;; attempt to unlock currently locked mutex
      (5 (if (!= cur-mtx *write-thread-id*)
           'unlocking-unowned-mtx
           (update prog-state `((write-thread . ,(destructor-thread 6 cur-sec-start cur-sec-end))
                                (mtxs . ,(update-nth buffer-write-idx 'free mtxs))))))
      ;; increment buffer-write-idx
      (6 (update prog-state `((write-thread . ,(destructor-thread 7 cur-sec-start cur-sec-end))
                              (buffer-write-idx . ,(mod (1+ buffer-write-idx) num-buffs)))))
      ;; attempt to lock next mutex
      (7 (if (== cur-mtx *write-thread-id*)
           'locking-owned-mtx
           (if (!= cur-mtx 'free)
             prog-state
             (update prog-state `((write-thread . ,(destructor-thread 8 cur-sec-start cur-sec-end))
                                  (mtxs . ,(update-nth buffer-write-idx *write-thread-id* mtxs)))))))
      ;; attempt to unlock writing mutex
      (8 (if (!= writing-mtx *write-thread-id*)
           'unlocking-unowned-mtx
           (update prog-state `((write-thread . ,(destructor-thread 9 cur-sec-start cur-sec-end))
                                (writing-mtx . free)))))
      ;; wait on read thread finishing
      (9 (if read-thread
           prog-state
           (update prog-state `((write-thread . ,(destructor-thread 10 cur-sec-start cur-sec-end))))))
      ;; unlock last buffer mutex
      (10 (if (!= cur-mtx *write-thread-id*)
            'unlocking-unowned-mtx
            (update prog-state `((write-thread . ,(destructor-thread 11 cur-sec-start cur-sec-end))
                                 (mtxs . ,(update-nth buffer-write-idx 'free mtxs))))))
      ;; close outfile, don't change write thread
      (11 (update prog-state `((outfile . (nil ,outfile)))))))
  :skip-tests t)#|ACL2s-ToDo-Line|#


