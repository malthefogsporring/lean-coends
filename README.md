## Formalising (co)ends in LEAN

We are formalising coends in LEAN. The LEAN file is in the **Projects** subfolder. 

The repository is a fork of the Lean for the Curious Mathematician 2023 [Github Repo](https://github.com/lftcm2023/lftcm2023).

## To use this repository on your computer

Do the following:

1. Install Lean 4 and VS Code following
   these [instructions](https://leanprover-community.github.io/get_started.html).

2. If you have not logged in since you installed Lean and mathlib, then you may need to first type `source ~/.profile` or `source ~/.bash_profile` depending on your OS.

3. Go the the directory where you would like this package to live.

4. Run `git clone https://github.com/malthefogsporring/lean-coends.git`.

5. Run `cd lean-coends`

6. Run `lake exe cache get`

7. Launch VS Code, either through your application menu or by typing `code .`. (MacOS users need to take a one-off [extra step](https://code.visualstudio.com/docs/setup/mac#_launching-from-the-command-line) to be able to launch VS Code from the command line.)

8. If you launched VS Code from a menu, on the main screen, or in the File menu, click "Open folder" (just "Open" on a Mac), and choose the folder `lftcm2023` (not one of its subfolders).
