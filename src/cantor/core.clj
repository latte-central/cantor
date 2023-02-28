(ns cantor.core
  (:require [nextjournal.clerk :as clerk])
  )

(defn start-clerk! []
  (clerk/serve! {:browse true, :watch-paths ["src"]}))


(comment
  (start-clerk!)
  (clerk/show! "src/cantor_bernstein/theorem.clj")
  )

(defn run [opts]
  (start-clerk!))


  

