Notes and Solutions to SICP
====
![SICP Cover](http://mitpress.mit.edu/sicp/full-text/book/cover.jpg "SICP Cover")
## Introduction

These are my notes and solutions to SICP. Notes are pretty verbose, an artifact of having had to memorize rote in the past~

## Where to get SICP

There are many ways to get SICP!

* The official site: http://mitpress.mit.edu/sicp/
* Nice pdf copy: http://sicpebook.wordpress.com/2011/05/28/new-electronic-sicp/
* Dead tree copy: At great bookstores everywhere

## How to work through SICP

To run examples and write solutions, I am running MIT/GNU Scheme as an emacs subprocess. (If you're new to emacs, don't be afraid! The emacs starter kit is a great place to start: https://github.com/technomancy/emacs-starter-kit)

You can download MIT/GNU Scheme as a binary here: http://www.gnu.org/software/mit-scheme/

Some helpful hooks for your .emacs:

```lisp
(setq scheme-program-name
      "/Applications/mit-scheme.app/Contents/Resources/mit-scheme")
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

All packages are available on Marmalade.