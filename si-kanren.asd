(defpackage :si-kanren-system
  (:use :common-lisp :asdf))

(in-package :si-kanren-system)

(defsystem "si-kanren"
  :version "0.1.0"
  :author "rgc"
  :license "MIT"
  :components ((:module "src"
                :serial t
                :components
                ((:file "si-kanren")
                 (:file "wrappers"))))


  :description "A micro-Kanren implementation in Common Lisp")
