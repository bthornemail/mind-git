#lang racket

;; Super Simple HTTP Server for Testing
(require web-server/servlet
         web-server/servlet-env)

;; Health endpoint - returns plain text for simplicity
(define (health-endpoint request)
  (response/full
   200
   #"OK"
   (current-seconds)
   #"text/plain"
   empty
   (list #"OK - Server is healthy")))

;; Generate endpoint - returns JSON as string
(define (generate-endpoint request)
  (response/full
   200
   #"OK"
   (current-seconds)
   #"application/json"
   (list (header #"Access-Control-Allow-Origin" #"*")
        (header #"Access-Control-Allow-Methods" #"POST, OPTIONS")
        (header #"Access-Control-Allow-Headers" #"Content-Type"))
   (list #"{\"success\":true,\"code\":\"#lang racket\\\\n\\\\n(define (main)\\\\n  (printf \\\"CanvasL Program~\\n\\\"))\\\\n\",\"metadata\":{\"lines\":4,\"language\":\"racket\"}}")))

;; CORS endpoint
(define (cors-endpoint request)
  (response/full
   200
   #"OK"
   (current-seconds)
   #"text/plain"
   (list (header #"Access-Control-Allow-Origin" #"*")
        (header #"Access-Control-Allow-Methods" #"POST, OPTIONS")
        (header #"Access-Control-Allow-Headers" #"Content-Type"))
   empty))

;; Routes
(define-values (dispatch generate-url)
  (dispatch-rules
   [("") health-endpoint]
   [("health") health-endpoint]
   [("generate") #:method "post" generate-endpoint]
   [("generate") #:method "options" cors-endpoint]))

;; Start server
(printf "🎯 Starting minimal Logos Racket server...~n")
(serve/servlet dispatch
               #:port 8080
               #:listen-ip "127.0.0.1"
               #:servlet-path "/"
               #:servlet-regexp #rx""
               #:command-line? #t)