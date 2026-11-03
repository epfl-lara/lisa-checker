# Continue on another machine

This archive contains the current project, its Git history and uncommitted work,
and a readable export of the conversation. Nothing was committed or reset in the
original repository to make this export.

## Quick start

1. Extract the entire archive, keeping its folder structure.
2. Open `project/` in VS Code or your coding agent. It is already a Git checkout;
   there is no patch or restoration script to run.
3. Install Git and Lean's `elan` toolchain manager if needed, and the Lean 4 VS Code
   extension if using VS Code. The project pins Lean and mathlib to **v4.29.1**.
4. From `project/`, run:

   ```text
   lake exe cache get
   lake build Lisa lisa-checker Tests
   ```

   The first run needs internet access to obtain the pinned toolchain/dependencies.
   `lake-manifest.json` is included; do not upgrade dependencies as part of the move.
   `.lake/` is deliberately excluded because its build products are machine-specific
   and the dependencies can be downloaded again. `lake exe cache get` is the command
   described by the mathlib dependency's local README at export time.

5. Start a conversation with your coding agent and paste:

   > Read `../HANDOFF.md` first. We are continuing the Lisa checker formalization.
   > The latest implementation task was system A and its translation to pure FOL.
   > A, canonical-form results, readback, and a conditional proof translation exist;
   > the concrete conservativity theorem is unfinished. Inspect
   > `Lisa/SCLambdaToPure/`, run the existing build, and continue from the outstanding
   > obligations described in the handoff. Consult `../conversation/CONVERSATION.md`
   > for earlier decisions when necessary. Preserve the existing uncommitted work.

## What is included

- `project/`: the source snapshot, tests, fixtures, paper, plans, archived OL code,
  and a freshly reconstructed `.git` directory preserving HEAD and the working changes.
- `HANDOFF.md`: current architecture, constraints, verification, and unfinished work.
- `conversation/CONVERSATION.md`: chronological user messages and assistant
  answers/updates, including the original IDE context and selections.
- `conversation/conversation.jsonl`: the same messages in structured form.
- `conversation/assets/`: the screenshot attached to the conversation.
- `repository.bundle`: an additional portable backup of all committed refs/history.
- `git-status.txt`, `staged.patch`, `unstaged.patch`, `deleted-tracked-files.txt`:
  records of the uncommitted state. **Do not apply these patches to `project/`:
  the changes are already there.**
- `source-manifest.json`: hashes of every source file in the snapshot.
- `MANIFEST.json` and `verify_export.py`: integrity verification for the full export.
- `verification/last-build.log`: the previously saved successful build log.
- `SNAPSHOT.json`: source commit, branch, timestamps, counts, and exclusions.

The copied checkout is on `simon-comments`. Its `origin` points to the included
`../repository.bundle`, not a hosting service. To resume pushing/pulling later,
set `origin` to your real repository URL. Git identity, authentication, original
local Git configuration/hooks/reflogs, editor settings outside the repository,
and Codex account settings are not transferred. Configure those on the new machine.
Keep the extracted outer folder if you want the offline bundle origin to work.

## Conversation portability

The transcript was recovered from this thread and its recorded ancestors, respecting
the exact branch cutoffs. It contains user-visible text and the attachment, rather
than internal tool logs or runtime state. `conversation/EXPORT_INFO.json` records
its coverage. It ends during the export request; it cannot include the final
delivery message that was sent after the archive was created.

The recommended continuation is a new conversation using the handoff. This export
is **not a native Codex chat-import file**, and no native cross-machine chat import
was tested. The official documentation describes `codex resume` for locally saved
chats; that does not by itself establish importing this transcript into another
installation. See [the official Codex CLI documentation](https://learn.chatgpt.com/docs/codex/cli).

## Verify the copied export

Before editing or building, run from the extracted outer folder:

```text
python verify_export.py
```

On Windows, `py verify_export.py` also works if Python is installed through the
standard launcher. Python is only needed for this optional verification, not for
building Lean. The accompanying `.zip.sha256` file checks the ZIP itself; on Windows
you can compare it with `Get-FileHash -Algorithm SHA256 <archive.zip>`.

The verifier reads files only. Git operations and builds will legitimately change
some copied `.git` files or add `.lake/`, so a full-export hash check is intended
for the initial extraction.
