(defpackage :eval-nld.system
  (:use :cl
	:asdf))

(in-package :eval-nld.system)

(defsystem "eval-nld"
    :description "An evaluation tool for nonlocal dependency identification"
    :version "0.1.1"
    :author "Yoshihide Kato"
    :components ((:file "eval-nld")))
