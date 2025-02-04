---
title: Introduction to proof assistants
usemathjax: true
---

## Installing Lean on your computer

The whole system is rather heavy on resources, but installing it should be
straightforward. Ensure that you have a fast connection before starting. Here is
what I advise you to do:

1. Collaboration will be **a lot** smoother if you have a
  [github](https://github.com/) account with an SSH key activated, details of
  how to do this depend on your system (and it is not strictly necessary). If
  you do, tell me what your github name is so that I can add you to the project.
2. Install VSCode, available at
   [https://code.visualstudio.com/](https://code.visualstudio.com/).
3. Within VSCode, install the `Lean 4` extension.
4. There should be a ∀-shaped button appearing in the top-right corner, click it
   and choose `Open Project...` then `Download project...` and enter the course
   URL in the dialog: either
   [git@github.com:vbeffara/Cours_ED.git](git@github.com:vbeffara/Cours_ED.git)
   if you did step 1, or
   [https://github.com/vbeffara/Cours_ED.git](https://github.com/vbeffara/Cours_ED.git)
   if you didn't. This will download the project to a folder you will choose on
   your computer.
5. VSCode will proceed to install all the necessary pieces for you, after asking
  for confirmation. (It is possible to install the system by hand, but it is a
  little involved if you want all the bells and whistles like pre-built
  libraries and everything, see here:
  [https://leanprover-community.github.io/get_started.html](https://leanprover-community.github.io/get_started.html).)
1. Choose to open the newly created project in VSCode.
2. That's it, you should now have a functional Lean system.
