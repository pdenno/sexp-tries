# sexp-tries

A Clojure library providing means to query a lightweight in-memory DB of s-expressions
implemented as tries. It is roughly based on the Tries code in Peter Norvig's book,
"Paradigms of Artificial Intelligence Programming"

## Usage

(ensure-trie-db :foo)
(with-trie-db (:foo)
  (trie-add '(hello world))
  (trie-add '(hello foo))
  (trie-add '(hello (bar)))
  (trie-query '(hello ?what)) ==> ((hello world)) (hello foo) (hello (bar)))

## License

Copyright © 2014 Peter Denno

Distributed under the Eclipse Public License either version 1.0.
