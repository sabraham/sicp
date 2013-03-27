Notes and Solutions to SICP
====

I am running MIT-GNU Scheme as an emacs subprocess. My .emacs:

```lisp
(require 'paredit)
(require 'highlight-parentheses)
(require 'xscheme)
(add-hook 'scheme-mode-hook
          (lambda ()
            (highlight-parentheses-mode t)
            (fci-mode t)
            (paredit-mode t)
            (set-fill-column 80)
            (setq hl-paren-colors
              '("red1" "orange1" "yellow1" "green1" "cyan1"
                "slateblue1" "magenta1" "purple"))))
```