;;; lf-mode.el --- Major mode for the LF -*- lexical-binding: t -*-

;; Author: Eugene Smolanka <esmolanka@gmail.com>
;; Version: 0.0.0
;; Keywords: languages
;; Package-Requires: ((emacs "24.3"))

;;; Commentary:

;; This library provides support for LF language.

;;; Code:

(load "flycheck" t t)

(defconst lf-mode-syntax-table
  (let ((table (make-syntax-table)))
    (modify-syntax-entry ?\; ". 12" table)
    (modify-syntax-entry ?\n ">" table)

    (modify-syntax-entry ?\  " "  table)
    (modify-syntax-entry ?\t " "  table)
    (modify-syntax-entry ?\" "\"" table)
    (modify-syntax-entry ?_ "_"   table)

    (modify-syntax-entry ?\( "()" table)
    (modify-syntax-entry ?\) ")(" table)
    (modify-syntax-entry ?\[ "(]" table)
    (modify-syntax-entry ?\] ")[" table)
    (modify-syntax-entry ?\{ "(}" table)
    (modify-syntax-entry ?\} "){" table)

    (mapc (lambda (x)
            (modify-syntax-entry x "." table))
            "!@#$%^&*+|/:.,~<>")
    table)
  "Syntax table for LF files.")

(defconst lf-keyword-keywords
  '("if"
    "case"
    "catch"
    "lambda"
    "do"
    "let"))

(defvar lf-font-lock-keywords
  `( ;; Keywords
     (,(rx symbol-start (eval `(or ,@lf-keyword-keywords)) symbol-end) .
      (0 font-lock-keyword-face))))

;;;###autoload
(define-derived-mode lf-mode prog-mode "LF"
  "Major mode for Lf"
  :syntax-table lf-mode-syntax-table
  (setq-local font-lock-defaults '(lf-font-lock-keywords))
  (setq-local indent-tabs-mode nil)
  (setq-local comment-start ";; ")
  (setq-local comment-start-skip ";;+\\s;* "))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.lf\\'" . lf-mode))

(when (featurep 'flycheck)
  (flycheck-define-checker lf
      "Checker for LF"
      :command ("lf" "--check" source-original)
      :error-patterns
      ((error
         line-start
         (file-name (+ not-newline) ".lf") ":"
         line ":"
         column
         (? "-"
            (+ digit) ":"
            (+ digit)) ":"
         (message (* not-newline)
                  (* (seq "\n"
                          (optional
                           (+ " ")
                           (+ not-newline)))))))
      :modes (lf-mode))
  (add-to-list 'flycheck-checkers 'lf))

(provide 'lf-mode)
;;; lf-mode.el ends here
