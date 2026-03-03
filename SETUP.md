---
title: Setup
nav_order: 3
---

# Setting Up a Lean Project

This guide walks through the full setup for working with Lean 4 and Mathlib, from installing developer tools to compiling your first files.


## 1. Install developer tools

You need **git** and a working terminal.

**macOS.**
Run `xcode-select --install` to get Apple's command-line tools, which include git.
[Homebrew](https://brew.sh) is recommended as a general package manager but not required.

**Linux.**
Install git via your package manager:
```bash
# Debian / Ubuntu
sudo apt install git

# Arch
sudo pacman -S git
```

**Windows.**
Install [WSL2](https://learn.microsoft.com/en-us/windows/wsl/install) (Windows Subsystem for Linux) with Ubuntu.
This is the officially recommended environment for Lean on Windows.
Git is then installed within WSL (`sudo apt install git`).
Keep your project files inside the WSL filesystem (e.g. `~/projects/`) rather than your Windows Documents folder.


## 2. Install Visual Studio Code

Download and install [VS Code](https://code.visualstudio.com).

**Windows/WSL users:** also install the [Remote - WSL](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-wsl) extension, then open VS Code from within WSL using `code .`.


## 3. Install Lean and the VS Code extension

**Install elan** (the Lean version manager):
```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

Follow the prompts and restart your terminal (or run `source ~/.profile`).

**Verify the installation:**
```bash
elan --version    # e.g. elan 4.x.x
lean --version    # e.g. Lean (version 4.28.0, ...)
lake --version    # e.g. Lake (version ...)
```

If `lean` is not found, ensure `~/.elan/bin` is on your `PATH`.

**Install the Lean 4 extension** in VS Code: search for `lean4` in the Extensions panel (or install [vscode-lean4](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)).

**The Lean Infoview.**
After installing the extension, the *Lean Infoview* panel appears in VS Code (toggle with `Ctrl+Shift+P` → "Lean 4: Infoview: Toggle").
This is your main feedback loop: it shows the current **goal state** (what remains to prove) and **context** (what hypotheses you have) as your cursor moves through a proof.
You will be reading the infoview constantly.


## 4. Create a GitHub account and set up SSH

If you do not yet have a GitHub account, create one at [github.com/signup](https://github.com/signup).

**Generate an SSH key** (if you don't already have one):
```bash
ssh-keygen -t ed25519 -C "your_email@example.com"
```

Press Enter to accept the default file location and set a passphrase if desired.

**Add the key to GitHub:**
```bash
cat ~/.ssh/id_ed25519.pub
```

Copy the output and add it at [github.com/settings/ssh/new](https://github.com/settings/ssh/new).

**Test the connection:**
```bash
ssh -T git@github.com
# Should print: Hi <username>! You've successfully authenticated, ...
```


## 5. Create a project on GitHub and clone it

1. Go to [github.com/new](https://github.com/new) and create a new repository (e.g. `MyLeanProject`).
   Add a `.gitignore` for Lean or leave it empty.

2. Clone the repository:
   ```bash
   git clone git@github.com:<username>/MyLeanProject.git
   cd MyLeanProject
   ```


## 6. Initialize a Mathlib-based Lean project

Inside your cloned repository, run:

```bash
lake init . math
```

This creates the project scaffolding in the current directory with Mathlib as a dependency.
The key files it generates:

| File | Purpose |
|------|---------|
| `lean-toolchain` | Pins the Lean version (e.g. `leanprover/lean4:v4.28.0`). Elan reads this to install the correct toolchain automatically. |
| `lakefile.toml` | Project configuration: package name, dependencies, build targets. The `[[require]]` section declares the Mathlib dependency. |
| `MyLeanProject.lean` | Root import file for your library. |

**Download the Mathlib cache** (this avoids compiling Mathlib from source, which takes hours):
```bash
lake exe cache get
```

This downloads pre-built `.olean` files for Mathlib.
It may take a few minutes on first run.

**Build the project:**
```bash
lake build
```

**Verify in VS Code.**
Open the project folder in VS Code (`code .`).
Create or open a `.lean` file, add `import Mathlib` at the top, and check that the Lean Infoview shows no errors.
The first load may take a moment as Lean indexes the project.


## 7. Verify: compile the three P01 files

If you are following this course, copy the three introductory files into your project:

```
BlockCourse/P01_Introduction/S04_TopologyExample.lean
BlockCourse/P01_Introduction/S04_NumberTheoryExample.lean
BlockCourse/P01_Introduction/S05_ProgrammingLanguage.lean
```

Build with:
```bash
lake build
```

All three files should compile.
Warnings (unused variables, `sorry`, `Try this` suggestions) are expected and fine.
Errors (red underlines in VS Code, `unknown identifier`, `type mismatch`) indicate a problem.


## 8. Troubleshooting

### Lean is compiling thousands of Mathlib files

The Mathlib cache was not downloaded or is stale.

1. Kill running Lean processes:
   ```bash
   # macOS / Linux
   pkill -f lean

   # Windows (PowerShell)
   Stop-Process -Name *lean* -Force
   ```

2. Remove the build cache and re-download:
   ```bash
   rm -rf .lake
   lake exe cache get
   ```

3. Restart the Lean server in VS Code:
   `Ctrl+Shift+P` → "Lean 4: Server: Restart Server"

### `lake` commands fail or behave unexpectedly

Lake's CLI changes between Lean versions.
If a command from a tutorial does not work, check:

```bash
lake --help
lake init --help
```

Common changes across versions:
- `lake init <name> math` initializes in the current directory with a Mathlib template.
  In some versions, `lake new <name> math` creates a new subdirectory instead.
- `lake exe cache get` downloads Mathlib's pre-built binaries.
  In older versions, this required `lake exe cache get!` (with `!`) to force overwrite.

### VS Code shows stale errors after edits

The Lean server sometimes gets out of sync.
Restart it via `Ctrl+Shift+P` → "Lean 4: Server: Restart Server".

### Nothing works

As a last resort:
```bash
rm -rf .lake
lake exe cache get
lake build
```

Then restart the Lean server in VS Code.
