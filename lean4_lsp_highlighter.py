#!/usr/bin/env python3
"""
Lean 4 LSP Syntax Highlighter
Retrieves syntactic and semantic information from Lean 4 LSP server
for accurate syntax highlighting.
"""

import json
import subprocess
import sys
from pathlib import Path
from typing import Optional, Dict, List, Any


class Lean4LSPClient:
    """Synchronous client for interacting with Lean 4 LSP server."""
    
    def __init__(self, lean_executable: str = "lake"):
        self.lean_exec = lean_executable
        self.process: Optional[subprocess.Popen] = None
        self.msg_id = 0
        
    def start(self):
        """Start the Lean 4 LSP server."""
        try:
            self.process = subprocess.Popen(
                [self.lean_exec, "serve", "--"],
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=False,
                bufsize=0
            )
            
            print("✓ Lean 4 LSP server started", file=sys.stderr)
            return True
        except Exception as e:
            print(f"✗ Failed to start Lean LSP server: {e}", file=sys.stderr)
            return False
    
    def _read_response(self) -> Optional[Dict]:
        """Read a single response from LSP server synchronously."""
        try:
            # Read headers
            headers = {}
            while True:
                line = self.process.stdout.readline().decode('utf-8')
                if line == '\r\n' or line == '\n':
                    break
                if ':' in line:
                    key, value = line.split(':', 1)
                    headers[key.strip()] = value.strip()
            
            # Read content
            if 'Content-Length' in headers:
                length = int(headers['Content-Length'])
                content = self.process.stdout.read(length).decode('utf-8')
                response = json.loads(content)
                return response
        except Exception as e:
            print(f"Error reading response: {e}", file=sys.stderr)
            return None
    
    def _send_message(self, message: Dict):
        """Send a JSON-RPC message to the server."""
        content = json.dumps(message)
        header = f"Content-Length: {len(content)}\r\n\r\n"
        
        self.process.stdin.write(header.encode('utf-8'))
        self.process.stdin.write(content.encode('utf-8'))
        self.process.stdin.flush()
    
    def _send_request(self, method: str, params: Dict) -> Optional[Dict]:
        """Send a request and wait for response synchronously."""
        self.msg_id += 1
        message = {
            "jsonrpc": "2.0",
            "id": self.msg_id,
            "method": method,
            "params": params
        }
        
        self._send_message(message)
        
        # Read responses until we get the one matching our request ID
        while True:
            response = self._read_response()
            if response is None:
                return None
            
            # Handle notifications (no id field)
            if 'id' not in response:
                continue
            
            # Check if this is our response
            if response.get('id') == self.msg_id:
                return response
    
    def _send_notification(self, method: str, params: Dict):
        """Send a notification (no response expected)."""
        message = {
            "jsonrpc": "2.0",
            "method": method,
            "params": params
        }
        self._send_message(message)
    
    def initialize(self, root_uri: str) -> bool:
        """Initialize the LSP server."""
        params = {
            "processId": None,
            "rootUri": root_uri,
            "capabilities": {
                "textDocument": {
                    "semanticTokens": {
                        "requests": {
                            "full": True
                        },
                        "tokenTypes": [],
                        "tokenModifiers": []
                    },
                    "documentSymbol": {},
                    "hover": {}
                }
            }
        }
        
        response = self._send_request("initialize", params)
        
        if response and 'result' in response:
            self.server_capabilities = response['result'].get('capabilities', {})
            
            # Send initialized notification
            self._send_notification("initialized", {})
            print("✓ LSP server initialized", file=sys.stderr)
            return True
        
        print("✗ Failed to initialize LSP server", file=sys.stderr)
        return False
    
    def open_document(self, uri: str, text: str):
        """Open a document in the LSP server."""
        params = {
            "textDocument": {
                "uri": uri,
                "languageId": "lean4",
                "version": 1,
                "text": text
            }
        }
        self._send_notification("textDocument/didOpen", params)
        
        # Read any diagnostics or notifications that come back
        # (they won't have an 'id' field so _send_request would skip them)
        import time
        time.sleep(0.1)  # Give server a moment to process
        self._drain_notifications()
    
    def _drain_notifications(self):
        """Drain any pending notifications from the server."""
        # Set a short timeout to check for notifications
        import select
        while True:
            # Check if data is available (with 0.1s timeout)
            ready, _, _ = select.select([self.process.stdout], [], [], 0.1)
            if not ready:
                break
            
            response = self._read_response()
            if response and 'id' not in response:
                # This is a notification, just consume it
                continue
            else:
                # This shouldn't happen, but if we get a request response, stop
                break
    
    def get_semantic_tokens(self, uri: str) -> Optional[List[int]]:
        """Get semantic tokens for syntax highlighting."""
        params = {
            "textDocument": {
                "uri": uri
            }
        }
        
        response = self._send_request("textDocument/semanticTokens/full", params)
        
        if response and 'result' in response:
            return response['result'].get('data', [])
        
        return None
    
    def get_document_symbols(self, uri: str) -> Optional[List[Dict]]:
        """Get document symbols (definitions, theorems, etc.)."""
        params = {
            "textDocument": {
                "uri": uri
            }
        }
        
        response = self._send_request("textDocument/documentSymbol", params)
        
        if response and 'result' in response:
            return response['result']
        
        return None
    
    def shutdown(self):
        """Shutdown the LSP server."""
        if self.process:
            self._send_request("shutdown", {})
            self._send_notification("exit", {})
            self.process.wait(timeout=2.0)
            print("✓ LSP server shutdown", file=sys.stderr)


def decode_semantic_tokens(data: List[int], lines: List[str]) -> List[Dict]:
    """
    Decode semantic tokens from LSP format.
    
    Format: [deltaLine, deltaStart, length, tokenType, tokenModifiers, ...]
    Each token is represented by 5 integers.
    """
    tokens = []
    current_line = 0
    current_start = 0
    
    i = 0
    while i < len(data):
        delta_line = data[i]
        delta_start = data[i + 1]
        length = data[i + 2]
        token_type = data[i + 3]
        token_modifiers = data[i + 4]
        
        # Update position
        current_line += delta_line
        if delta_line == 0:
            current_start += delta_start
        else:
            current_start = delta_start
        
        # Extract token text
        if current_line < len(lines):
            line = lines[current_line]
            token_text = line[current_start:current_start + length]
        else:
            token_text = ""
        
        tokens.append({
            "line": current_line,
            "start": current_start,
            "length": length,
            "type": token_type,
            "modifiers": token_modifiers,
            "text": token_text
        })
        
        i += 5
    
    return tokens


# Standard LSP semantic token types
TOKEN_TYPES = [
    "namespace", "type", "class", "enum", "interface", "struct", "typeParameter",
    "parameter", "variable", "property", "enumMember", "event", "function",
    "method", "macro", "keyword", "modifier", "comment", "string", "number",
    "regexp", "operator"
]

# Token type to color mapping (for terminal output)
TOKEN_COLORS = {
    "keyword": "\033[95m",      # Magenta
    "function": "\033[94m",     # Blue
    "method": "\033[94m",       # Blue
    "type": "\033[96m",         # Cyan
    "class": "\033[96m",        # Cyan
    "variable": "\033[92m",     # Green
    "parameter": "\033[92m",    # Green
    "string": "\033[93m",       # Yellow
    "number": "\033[93m",       # Yellow
    "comment": "\033[90m",      # Gray
    "namespace": "\033[35m",    # Purple
    "operator": "\033[91m",     # Red
}
RESET = "\033[0m"


def highlight_lean_code(file_path: str, lean_exec: str = "lake"):
    """Main function to highlight Lean code using LSP server."""
    
    # Read the Lean file
    path = Path(file_path)
    if not path.exists():
        print(f"Error: File '{file_path}' not found", file=sys.stderr)
        return
    
    with open(path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    lines = content.splitlines()
    
    # Start LSP client
    client = Lean4LSPClient(lean_exec)
    if not client.start():
        return
    
    # Initialize with project root
    root_path = path.parent.absolute()
    root_uri = f"file://{root_path}"
    
    if not client.initialize(root_uri):
        client.shutdown()
        return
    
    # Open document
    file_uri = f"file://{path.absolute()}"
    client.open_document(file_uri, content)
    
    # Give server time to process
    import time
    time.sleep(2)
    
    # Get semantic tokens
    print("Fetching semantic tokens...", file=sys.stderr)
    semantic_data = client.get_semantic_tokens(file_uri)
    
    if semantic_data:
        tokens = decode_semantic_tokens(semantic_data, lines)
        print(f"✓ Found {len(tokens)} semantic tokens\n", file=sys.stderr)
        
        # Print token information
        print("=== SEMANTIC TOKENS ===")
        for token in tokens[:20]:  # Show first 20 tokens
            token_type_name = TOKEN_TYPES[token['type']] if token['type'] < len(TOKEN_TYPES) else f"unknown({token['type']})"
            print(f"Line {token['line']+1}, Col {token['start']}: "
                  f"'{token['text']}' -> {token_type_name}")
        
        if len(tokens) > 20:
            print(f"... and {len(tokens) - 20} more tokens")
        
        print("\n=== HIGHLIGHTED CODE ===")
        # Apply colors
        for line_num, line in enumerate(lines):
            colored_line = line
            line_tokens = [t for t in tokens if t['line'] == line_num]
            line_tokens.sort(key=lambda t: t['start'], reverse=True)
            
            for token in line_tokens:
                token_type_name = TOKEN_TYPES[token['type']] if token['type'] < len(TOKEN_TYPES) else "unknown"
                color = TOKEN_COLORS.get(token_type_name, "")
                
                if color:
                    start = token['start']
                    end = start + token['length']
                    colored_line = (colored_line[:start] + color + 
                                  colored_line[start:end] + RESET + 
                                  colored_line[end:])
            
            print(f"{line_num+1:4d} | {colored_line}")
    else:
        print("✗ No semantic tokens received", file=sys.stderr)
    
    # Get document symbols
    print("\n=== DOCUMENT SYMBOLS ===", file=sys.stderr)
    symbols = client.get_document_symbols(file_uri)
    
    if symbols:
        print(json.dumps(symbols, indent=2))
    else:
        print("No symbols found", file=sys.stderr)
    
    # Shutdown
    client.shutdown()


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python lean4_lsp_highlighter.py <lean_file.lean> [lean_executable]")
        print("Example: python lean4_lsp_highlighter.py MyFile.lean")
        print("         python lean4_lsp_highlighter.py MyFile.lean lake")
        sys.exit(1)
    
    lean_file = sys.argv[1]
    lean_exec = sys.argv[2] if len(sys.argv) > 2 else "lake"
    
    highlight_lean_code(lean_file, lean_exec)
