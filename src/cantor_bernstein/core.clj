(ns cantor-bernstein.core
  (:require [nextjournal.clerk :as clerk])
  )

(defn start-clerk! []
  (clerk/serve! {:watch-paths ["src"]}))


(comment
  (clerk/show! "src/cantor_bernstein/theorem.clj")
  )

(defn run [opts]
  (start-clerk!))


  

