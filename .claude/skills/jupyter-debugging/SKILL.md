---
name: jupyter-debugging
description: "Interactive debugging via Jupyter Lab + the jupyter MCP server: start it with direnv exec . start-jupyter-lab (detached screen session), token handling, restart procedure, and the rule to use .local.ipynb notebooks instead of python heredocs for temporary code execution. Use when debugging interactively or running throwaway code."
---

# Jupyter Lab for MCP Server

This project includes a Jupyter Lab server that can be used with the `jupyter` MCP (Model Context Protocol) server for notebook-based debugging and development.

> **IMPORTANT:** Do NOT use Python command line with heredoc (e.g., `python << 'EOF'`) for temporary code execution or debugging. Instead, ALWAYS use the Jupyter MCP server to create and run code in `<your-file-name>.local.ipynb` notebooks. These local notebooks are gitignored and provide a better debugging experience with persistent state and output history.

**Starting Jupyter Lab:**

```bash
direnv exec . start-jupyter-lab
```

This command:
- Starts Jupyter Lab in a detached `screen` session, which can be connected by the `jupyter` MCP server tools
- Creates a session named `jupyter-<directory-name>` that persists in the background

**Token Management:**

- If `JUPYTER_TOKEN` is not set, the script generates a secure random token
- The token is automatically saved to [.env](.env) to maintain consistency across sessions
- Subsequent launches will reuse the same token from [.env](.env)

**Session Management:**

The Jupyter Lab server runs in a detached `screen` session, which means:
- It continues running in the background after the command completes
- You can check the logs by enabling logging and tailing the file `%S.%n.local.screenlog`

**Restarting Jupyter Lab:**

To stop an existing Jupyter Lab server and start a new one:

```bash
# Stop the current Jupyter Lab server
direnv exec . jupyter server stop

# IMPORTANT: Do NOT terminate the Jupyter Lab server with abrupt kill commands such as `kill`, `pkill`, or `screen -X quit` unless explicitly requested.

# Start a new Jupyter Lab server
direnv exec . start-jupyter-lab
```

This is necessary when dependencies are updated (e.g., [flake.lock](flake.lock), [uv.lock](uv.lock)) and you need the Jupyter Lab server to use the new environment with updated packages.

**Usage with MCP:**

Once Jupyter Lab is running, the `jupyter` MCP server tools can connect to it for:
- Creating and managing notebooks programmatically
- Executing code cells for debugging
- Reading notebook outputs and results

