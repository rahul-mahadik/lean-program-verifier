"""A prompt-only Codex subprocess, with an audited JSON event stream."""

from __future__ import annotations

import json
import hashlib
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import time

SCHEMA = {
    "type": "object",
    "properties": {
        "invariant": {"type": "string"},
        "variant": {"type": "string"},
        "solver": {"type": "string", "enum": ["omega", "nonlinear"]},
    },
    "required": ["invariant", "variant", "solver"],
    "additionalProperties": False,
}


def audit_events(text: str) -> dict:
    """Fail closed: successful runs contain messages/reasoning, never tool items."""
    allowed_events = {"thread.started", "turn.started", "turn.completed",
                      "item.started", "item.updated", "item.completed"}
    allowed_items = {"agent_message", "reasoning"}
    events = []
    phase = "new"
    for line in text.splitlines():
        event = json.loads(line)
        if not isinstance(event, dict) or event.get("type") not in allowed_events:
            raise ValueError("Unexpected or failed Codex event")
        kind = event["type"]
        if kind == "thread.started" and phase == "new":
            phase = "thread"
        elif kind == "turn.started" and phase == "thread":
            phase = "turn"
        elif kind == "turn.completed" and phase == "turn":
            phase = "done"
        elif kind.startswith("item.") and phase == "turn":
            item = event.get("item")
            if not isinstance(item, dict) or item.get("type") not in allowed_items:
                raise ValueError("Model used a tool; attempt excluded from verified successes")
            if kind == "item.completed" and item["type"] == "agent_message":
                if not isinstance(item.get("text"), str):
                    raise ValueError("Invalid model message")
        else:
            raise ValueError("Invalid event lifecycle")
        events.append(event)
    completed = [e for e in events if e["type"] == "turn.completed"]
    if len(completed) != 1 or not events or events[-1]["type"] != "turn.completed":
        raise ValueError("Missing successful final turn event")
    messages = [e["item"]["text"] for e in events
                if e["type"] == "item.completed"
                and e["item"]["type"] == "agent_message"]
    if not messages:
        raise ValueError("No final model message")
    return {"tool_items": 0, "usage": completed[0].get("usage", {}),
            "last_message": messages[-1]}


def propose(prompt: str, directory: Path, model: str, timeout: float,
            executable: str = "codex", effort: str = "medium") -> dict:
    directory.mkdir(parents=True, exist_ok=True)
    (directory / "prompt.txt").write_text(prompt)
    schema = directory / "schema.json"
    schema.write_text(json.dumps(SCHEMA, indent=2) + "\n")
    output = directory / "response.json"
    output.unlink(missing_ok=True)
    cli = shutil.which(executable)
    if cli is None:
        return {"status": "provider_error", "error": "Codex CLI executable not found"}
    if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9._/-]{0,120}", model):
        raise ValueError("Invalid model identifier")
    if effort not in {"low", "medium", "high", "xhigh", "max", "ultra"}:
        raise ValueError("Invalid reasoning effort")
    start = time.monotonic()
    # No repository, reference answers, diagnostics, or project files are copied here.
    with tempfile.TemporaryDirectory(prefix="lean-proposal-") as isolated:
        command = [cli, "--no-daemon", "exec", "--ignore-user-config", "--ignore-rules",
                   "--ephemeral", "--json", "--strict-config", "--sandbox", "read-only",
                   "--skip-git-repo-check", "--model", model,
                   "-c", f'model_reasoning_effort="{effort}"',
                   "-c", "project_doc_max_bytes=0",
                   "-c", "skills.bundled.enabled=false", "-c", "skills.include_instructions=false",
                   "-c", 'web_search="disabled"', "-C", isolated,
                   "--output-schema", str(schema.resolve()),
                   "--output-last-message", str(output.resolve()), "-"]
        for feature in ("apps", "plugins", "multi_agent", "browser_use", "computer_use",
                        "view_image", "sleep_tool", "goals", "hooks", "memories",
                        "shell_snapshot", "workspace_dependencies", "skill_search",
                        "tool_suggest", "shell_tool"):
            command[-1:-1] = ["--disable", feature]
        try:
            process = subprocess.run(command, input=prompt, text=True, capture_output=True,
                                     timeout=timeout, check=False)
            stdout, stderr = process.stdout, process.stderr
            status = "ok" if process.returncode == 0 else "provider_error"
            error = None if status == "ok" else f"Codex exited {process.returncode}"
        except subprocess.TimeoutExpired as exc:
            stdout = exc.stdout or b""
            stderr = exc.stderr or b""
            stdout = stdout.decode(errors="replace") if isinstance(stdout, bytes) else stdout
            stderr = stderr.decode(errors="replace") if isinstance(stderr, bytes) else stderr
            status, error = "provider_timeout", "Model generation exceeded time limit"
        stdout, stderr = stdout.replace(isolated, "<isolated>"), stderr.replace(isolated, "<isolated>")
    (directory / "events.jsonl").write_text(stdout)
    (directory / "provider.log").write_text(stderr)
    result = {"status": status, "model": model, "reasoning_effort": effort,
              "invocation": [a.replace(isolated, "<isolated>").replace(str(directory.resolve()), "<attempt>")
                             for a in command],
              "cli_sha256": hashlib.sha256(Path(cli).read_bytes()).hexdigest(),
              "generation_seconds": round(time.monotonic() - start, 3), "error": error}
    if status != "ok":
        return result
    try:
        audit = audit_events(stdout)
        candidate = json.loads(output.read_text())
        if candidate != json.loads(audit.pop("last_message")):
            raise ValueError("Output file differs from final model event")
        result.update(audit)
        result["candidate"] = candidate
    except (ValueError, OSError, KeyError, TypeError) as exc:
        result.update(status="invalid_response", error=str(exc))
    return result
