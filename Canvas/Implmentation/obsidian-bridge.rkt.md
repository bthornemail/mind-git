#lang racket

(require json
         racket/thread
         racket/file ; for file-or-directory-modify-seconds, file-exists?, path-only
         racket/date ; for seconds->date, date->string
         racket/path ; for build-path)

;; obsidian-canvas.rkt - Bridge to Obsidian Canvas for visual organization
;; Start small, grow organically

(provide start-obsidian-bridge
         canvas-state->logos
         logos->canvas-state
         watch-canvas-file)

;; ============================================================================
;; 1. BASIC STRUCTURES (Start simple)
;; ============================================================================

;; A canvas node - simplified version
(struct canvas-node (id x y width height content color)
  #:transparent
  #:mutable)

;; A canvas edge - simplified version
(struct canvas-edge (id from to label color)
  #:transparent
  #:mutable)

;; Canvas state - just nodes and edges for now
(struct canvas-state (nodes edges)
  #:transparent)

;; ============================================================================
;; 2. FILE WATCHER (Your most important tool - Polling mechanism)
;; ============================================================================

(define (watch-canvas-file path callback)
  ;; Watch a canvas file for changes, call callback when it changes
  (printf "Watching canvas file: ~a\n" path)

  (thread
    (λ ()
      (let loop ([last-modified 0])
        (sleep 1)  ;; Check every second
        (when (file-exists? path)
          (let ([modified (file-or-directory-modify-seconds path)])
            (when (> modified last-modified)
              (printf "Canvas file changed! (~a)\n" (date->string (seconds->date modified) #t))
              (callback path)
              (loop modified))
            (loop last-modified)))))))

;; Placeholder for directory watching, using polling
(define (watch-directory path callback)
  (printf "Watching directory for code changes: ~a\n" path)
  (thread
    (λ ()
      (let loop ([last-modified 0])
        (sleep 5) ;; Check every 5 seconds (less frequently than canvas)
        (when (directory-exists? path)
          ;; Note: checking the directory's modify time is a weak signal.
          ;; A robust system would traverse files. We keep it simple here.
          (let ([modified (file-or-directory-modify-seconds path)])
            (when (> modified last-modified)
              (printf "Code directory changed! (~a)\n" (date->string (seconds->date modified) #t))
              ;; The callback needs the file that changed, but polling the directory
              ;; only gives the directory's change time. We notify that a code change
              ;; likely occurred.
              (callback path 'directory-changed)
              (loop modified))
            (loop last-modified)))))))

;; ============================================================================
;; 3. JSON PARSING (Simple, works with Obsidian format)
;; ============================================================================

(define (parse-canvas-json json-str)
  ;; Parse Obsidian Canvas JSON into our structures
  (let* ([data (string->jsexpr json-str)]
         [nodes (hash-ref data 'nodes (hash))]
         [edges (hash-ref data 'edges (hash))])

    ;; Convert to our structures
    (canvas-state
     (for/list ([(node-id node-data) (in-hash nodes)])
       (canvas-node
         (symbol->string node-id) ; IDs are strings in struct, symbols in parsed JSON
         (hash-ref node-data 'x 0)
         (hash-ref node-data 'y 0)
         (hash-ref node-data 'width 200)
         (hash-ref node-data 'height 150)
         (hash-ref node-data 'text "")
         (hash-ref node-data 'color "1")))

     (for/list ([(edge-id edge-data) (in-hash edges)])
       (canvas-edge
         (symbol->string edge-id)
         (hash-ref edge-data 'fromNode "")
         (hash-ref edge-data 'toNode "")
         (hash-ref edge-data 'label "")
         (hash-ref edge-data 'color "2"))))))

;; ============================================================================
;; 4. LOGOS MAPPING (Start with identity mapping)
;; ============================================================================

(define (canvas-state->logos canvas)
  ;; Map canvas state to Logos representation
  ;; For now, just pass through - we'll enhance this later

  (printf "Canvas -> Logos: ~a nodes, ~a edges\n"
          (length (canvas-state-nodes canvas))
          (length (canvas-state-edges canvas)))

  ;; Return a simple hash representing the state
  (hash
   'type 'canvas-state
   'nodes-count (length (canvas-state-nodes canvas))
   'edges-count (length (canvas-state-edges canvas))
   'canvas canvas))

(define (logos->canvas-state logos-data)
  ;; Convert Logos state back to canvas
  ;; For now, assume logos-data is a canvas-state
  (if (canvas-state? logos-data)
      logos-data
      (canvas-state '() '())))

;; ============================================================================
;; 5. TEMPLATE & SCANNING LOGIC
;; ============================================================================

(define (create-your-actual-structure)
  ;; Create a canvas that matches YOUR Polynomial/E8 research structure

  (define your-canvas
    (canvas-state
      ;; Polynomial orders 0-7
      (list
       (canvas-node "p0" -800 0 300 180 "Polynomial Order 0\n$0! = 1$\nSeed" "1")
       (canvas-node "p1" -400 0 300 180 "Polynomial Order 1\n$f_1(x) = x$\nSuccessor" "2")
       (canvas-node "p2" 0 0 300 180 "Polynomial Order 2\n$f_2(x) = x^2$\nPair" "3")
       (canvas-node "p3" 400 0 300 180 "Polynomial Order 3\n$f_3(x) = x^3$\nSpace" "4")
       (canvas-node "p4" -800 300 300 180 "Polynomial Order 4\n$f_4(x) = x^4$\nNetwork" "5")
       (canvas-node "p5" -400 300 300 180 "Polynomial Order 5\n$f_5(x) = x^5$\nConsensus" "6")
       (canvas-node "p6" 0 300 300 180 "Polynomial Order 6\n$f_6(x) = x^6$\nIntelligence" "7")
       (canvas-node "p7" 400 300 300 180 "Polynomial Order 7\n$f_7(x) = x^7$\nQuantum" "8"))

      ;; Connections between them
      (list
       (canvas-edge "e0-1" "p0" "p1" "$0\\to 1D$" "1")
       (canvas-edge "e1-2" "p1" "p2" "$1\\to 2D$" "2")
       (canvas-edge "e2-3" "p2" "p3" "$2\\to 3D$" "3")
       (canvas-edge "e3-4" "p3" "p4" "$3\\to 4D$" "4")
       (canvas-edge "e4-5" "p4" "p5" "$4\\to 5D$" "5")
       (canvas-edge "e5-6" "p5" "p6" "$5\\to 6D$" "6")
       (canvas-edge "e6-7" "p6" "p7" "$6\\to 7D$" "7")
       (canvas-edge "cycle" "p7" "p0" "$7\\to 0D$ (cycle)" "8"))))

  your-canvas)

(define (scan-research-files->canvas)
  ;; Scan your devopsmain directory and create canvas nodes

  (printf "Scanning research files...\n")

  (define research-areas
    (list
     (cons "automata-metaverse" "Metaverse with real physics")
     (cons "automaton" "Automata research platform")
     (cons "Axiomatic" "Formal verification system")
     (cons "epistemic-observability-engine" "Consciousness modeling")
     (cons "hyperbolic-geometric-neural-network" "Geometric ML")))

  (canvas-state
    ;; Create nodes for each research area
    (for/list ([area research-areas] [i (in-naturals)])
      (match-define (cons name description) area)
      (canvas-node
       name
       (* (modulo i 3) 500)       ; x position
       (* (quotient i 3) 300)     ; y position
       350 200                     ; width, height
       (format "# ~a\n\n~a" name description)
       (number->string (+ (modulo i 7) 1))))

    ;; Connect related areas (you define the connections)
    (list
     (canvas-edge "axiomatic->epistemic" "Axiomatic" "epistemic-observability-engine" "formalizes" "2")
     (canvas-edge "automaton->metaverse" "automaton" "automata-metaverse" "powers" "3"))))

;; ============================================================================
;; 6. TEMPLATE CREATION (Now takes a canvas-state object to write)
;; ============================================================================

(define (create-template-canvas path initial-canvas)
  ;; Create a template canvas file for Obsidian from a canvas-state struct
  
  (define nodes-hash (make-hash))
  (for ([node (canvas-state-nodes initial-canvas)])
    (hash-set! nodes-hash
               (string->symbol (canvas-node-id node)) ; Obsidian uses strings in final file, but Racket JSON parser likes symbols
               (hash 'id (canvas-node-id node)
                     'x (canvas-node-x node)
                     'y (canvas-node-y node)
                     'width (canvas-node-width node)
                     'height (canvas-node-height node)
                     'text (canvas-node-content node)
                     'color (canvas-node-color node))))
  
  (define edges-hash (make-hash))
  (for ([edge (canvas-state-edges initial-canvas)])
    (hash-set! edges-hash
               (string->symbol (canvas-edge-id edge))
               (hash 'id (canvas-edge-id edge)
                     'fromNode (canvas-edge-from edge)
                     'toNode (canvas-edge-to edge)
                     'label (canvas-edge-label edge)
                     'color (canvas-edge-color edge))))

  (define template
    (jsexpr->string
     (hash 'nodes nodes-hash
           'edges edges-hash)))
  
  ;; Ensure directory exists
  (define dir (path-only path))
  (when dir (make-directory* dir))
  
  ;; Write template
  (with-output-to-file path
    (λ () (display template))
    #:exists 'replace)
  
  (printf "Created template canvas at: ~a\n" path)
  (printf "Open this file in Obsidian Canvas to begin.\n"))

;; ============================================================================
;; 7. TWO-WAY SYNC LOGIC
;; ============================================================================

(define (update-research-structure-from-canvas canvas-path)
  ;; When you rearrange nodes in Obsidian, update your project structure
  (let* ([data (file->string canvas-path)]
         [canvas (parse-canvas-json data)]
         [nodes (canvas-state-nodes canvas)])

    (printf "Canvas has ~a research nodes\n" (length nodes))

    ;; For now, just log the positions
    (for ([node nodes])
      (printf "  Node: ~a at (~a, ~a)\n"
              (canvas-node-id node)
              (canvas-node-x node)
              (canvas-node-y node)))))

(define (update-canvas-from-code-changes path event)
  (printf "Code changes in ~a detected. Logic to generate new canvas state and save it goes here.\n" path)
  ;; This is where Logos logic would analyze the code structure and save a new canvas JSON.
  ;; For example, finding a new file might create a new node, or finding a new
  ;; Racket `provide` statement might create a new edge.
  )

(define (setup-two-way-sync canvas-path)
  ;; Watch canvas for changes AND watch your code files

  ;; 1. Canvas → Code sync
  (watch-canvas-file canvas-path
    (λ (path)
      (printf "Canvas changed -> updating code structure...\n")
      (update-research-structure-from-canvas path)))

  ;; 2. Code → Canvas sync
  (watch-directory (expand-user-path "~/devopsmain")
    (λ (path event)
      (when (and (directory-exists? path) ; Ensure it's a valid directory path
                 (not (regexp-match? #rx"\\/\\." path))) ; Skip dot-directories
        (printf "Code base potentially changed -> updating canvas...\n")
        (update-canvas-from-code-changes path event)))))

;; ============================================================================
;; 8. OBSIDIAN BRIDGE (Main entry point)
;; ============================================================================

(define (start-obsidian-bridge [canvas-path #f])
  ;; Start the bridge to Obsidian Canvas

  (let ([path (or canvas-path
                  (expand-user-path "~/Obsidian/Logos.canvas")
                  (expand-user-path "~/Documents/Obsidian/Logos.canvas"))])

    (printf "=== Starting Obsidian Canvas Bridge ===\n")
    (printf "Looking for canvas file at: ~a\n" path)

    (if (file-exists? path)
        (begin
          (printf "Found canvas file! Loading...\n")

          ;; Load initial state (optional, just for logging)
          (define initial-data (file->string path))
          (define canvas (parse-canvas-json initial-data))

          ;; Start two-way synchronization
          (setup-two-way-sync path) ; <--- Calls your new powerful two-way sync

          (printf "Obsidian Canvas bridge is active and watching for changes.\n")
          canvas)

        (begin
          (printf "Canvas file not found. Creating template with E8 polynomial structure...\n")
          ;; Use your defined structure for the initial template
          (create-template-canvas path (create-your-actual-structure))
          ;; Recurse to start the watcher on the new file
          (start-obsidian-bridge path)))))


;; ============================================================================
;; 9. UTILITIES (Helpers you'll need)
;; ============================================================================

(define (expand-user-path path-str)
  ;; Expand ~ to home directory
  (cond
    [(string-prefix? path-str "~/")
     (build-path (find-system-path 'home-dir) (substring path-str 2))]
    [else path-str]))

(define (list-canvas-nodes canvas)
  ;; List all nodes in a canvas
  (map canvas-node-id (canvas-state-nodes canvas)))

(define (find-node-by-id canvas node-id)
  ;; Find a node by ID
  (findf (λ (node) (equal? (canvas-node-id node) node-id))
         (canvas-state-nodes canvas)))

;; ============================================================================
;; 10. TEST FUNCTION (Run this to verify)
;; ============================================================================

(module+ test
  (printf "\n=== Testing Obsidian Canvas Bridge ===\n")

  ;; Test with a simple in-memory canvas
  (define test-canvas
    (canvas-state
      (list (canvas-node "test1" 0 0 200 150 "Test node" "1"))
      (list (canvas-edge "edge1" "test1" "test1" "self" "2"))))

  (printf "Test canvas created: ~a node, ~a edge\n"
          (length (canvas-state-nodes test-canvas))
          (length (canvas-state-edges test-canvas)))

  (printf "Canvas -> Logos conversion: ~a\n" (canvas-state->logos test-canvas))
  (printf "Test passed!\n"))

(module+ main
  ;; Run the bridge if this file is executed directly
  (start-obsidian-bridge))