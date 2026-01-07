#!/usr/bin/env python3
"""
Script to display Lean context at each line using the Lean Language Server Protocol.
Completely synchronous version - one request at a time.
"""

import json
import subprocess
import sys
import time
from pathlib import Path


class LeanLSPClient:
    def __init__(self, lean_file):
        self.lean_file = Path(lean_file).resolve()
        self.process = None
        self.msg_id = 0
        self.project_root = self.find_project_root()
        
    def find_project_root(self):
        """Find the Lean project root by looking for lakefile.lean or lean-toolchain"""
        current = self.lean_file.parent
        
        while current != current.parent:  # Stop at filesystem root
            if (current / 'lakefile.lean').exists() or \
               (current / 'lakefile.toml').exists() or \
               (current / 'lean-toolchain').exists():
                return current
            current = current.parent
        
        # If not found, use the file's directory
        return self.lean_file.parent
        
    def start_server(self):
        """Start the Lean LSP server from the project root"""
        print(f"Project root: {self.project_root}")
        
        self.process = subprocess.Popen(
            ['lean', '--server'],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            bufsize=0,
            cwd=str(self.project_root)
        )
        
    def send_message(self, message_dict):
        """Send a JSON-RPC message to the server"""
        message = json.dumps(message_dict)
        message_bytes = message.encode('utf-8')
        content_length = len(message_bytes)
        
        header = f"Content-Length: {content_length}\r\n\r\n".encode('utf-8')
        self.process.stdin.write(header + message_bytes)
        self.process.stdin.flush()
        
    def read_message(self):
        """Read exactly one JSON-RPC message from the server"""
        # Read headers
        headers = {}
        while True:
            line = b''
            while True:
                char = self.process.stdout.read(1)
                if not char:
                    raise EOFError("Stream ended unexpectedly")
                line += char
                if line.endswith(b'\n'):
                    break
            
            line = line.decode('utf-8', errors='replace')
            if line == '\r\n' or line == '\n':
                break
            if ':' in line:
                key, value = line.split(':', 1)
                headers[key.strip()] = value.strip()
        
        # Read exactly content_length bytes
        content_length = int(headers.get('Content-Length', 0))
        content_bytes = b''
        while len(content_bytes) < content_length:
            chunk = self.process.stdout.read(content_length - len(content_bytes))
            if not chunk:
                raise EOFError("Stream ended while reading message body")
            content_bytes += chunk
        
        content = content_bytes.decode('utf-8')
        return json.loads(content)
        
    def send_request_and_wait(self, method, params):
        """Send a request and wait for its response (ignoring notifications)"""
        self.msg_id += 1
        request = {
            "jsonrpc": "2.0",
            "id": self.msg_id,
            "method": method,
            "params": params
        }
        
        self.send_message(request)
        
        # Wait for the response with this ID
        while True:
            msg = self.read_message()
            
            # If it's a notification, just skip it
            if 'method' in msg:
                continue
            
            # If it's our response, return it
            if 'id' in msg and msg['id'] == self.msg_id:
                return msg
                
    def send_notification(self, method, params):
        """Send a notification (no response expected)"""
        notification = {
            "jsonrpc": "2.0",
            "method": method,
            "params": params
        }
        self.send_message(notification)
        
    def initialize(self):
        """Initialize the LSP session"""
        root_uri = self.project_root.absolute().as_uri()
        
        response = self.send_request_and_wait("initialize", {
            "processId": None,
            "rootUri": root_uri,
            "capabilities": {
                "textDocument": {
                    "hover": {
                        "contentFormat": ["plaintext", "markdown"]
                    }
                }
            }
        })
        
        # Send initialized notification
        self.send_notification("initialized", {})
        
        return response
        
    def open_file(self):
        """Open the Lean file"""
        with open(self.lean_file, 'r') as f:
            text = f.read()
            
        uri = self.lean_file.absolute().as_uri()
        
        self.send_notification("textDocument/didOpen", {
            "textDocument": {
                "uri": uri,
                "languageId": "lean",
                "version": 1,
                "text": text
            }
        })
        
        return text
        
    def get_plain_goal(self, line, character):
        """Get proof state (goals and hypotheses) at a specific position"""
        uri = self.lean_file.absolute().as_uri()
        
        response = self.send_request_and_wait("$/lean/plainGoal", {
            "textDocument": {"uri": uri},
            "position": {"line": line, "character": character}
        })
        
        return response
        
    def shutdown(self):
        """Shutdown the LSP server"""
        try:
            self.send_request_and_wait("shutdown", {})
            self.send_notification("exit", {})
            # Give it a moment to exit gracefully
            self.process.wait(timeout=2)
        except:
            # If it doesn't exit cleanly, kill it
            self.process.kill()
            self.process.wait()


def main():
    if len(sys.argv) != 2:
        print("Usage: python lean_lsp_context.py <lean_file>")
        sys.exit(1)
        
    lean_file = sys.argv[1]
    
    if not Path(lean_file).exists():
        print(f"Error: File '{lean_file}' not found")
        sys.exit(1)
        
    print(f"Analyzing {lean_file}...")
    
    client = LeanLSPClient(lean_file)
    
    # Check if we found a project root
    if not (client.project_root / 'lakefile.lean').exists() and \
       not (client.project_root / 'lakefile.toml').exists():
        print("\n⚠️  WARNING: No lakefile found in project root!")
        print(f"Project root: {client.project_root}")
        print("\nIf your file imports Mathlib or other dependencies,")
        print("make sure to run this script from within a Lean project directory.")
        print()
    
    print("=" * 80)
    
    try:
        # Start and initialize the server
        client.start_server()
        print("Initializing LSP server...")
        client.initialize()
        
        # Open the file
        print("Opening file...")
        text = client.open_file()
        lines = text.split('\n')
        
        # Wait for the server to process the file
        print("Waiting for server to process file...")
        time.sleep(3)
        
        # Query context at each line
        for line_num, line_text in enumerate(lines):
            if not line_text.strip():  # Skip empty lines
                continue
                
            print(f"\n{'=' * 80}")
            print(f"Line {line_num + 1}: {line_text}")
            print('-' * 80)
            
            found_context = False
            
            # Try to get proof state at different positions on the line
            for char_pos in range(0, min(len(line_text), 50)):
                if char_pos < len(line_text) and line_text[char_pos] not in (' ', '\t', '\n'):
                    try:
                        response = client.get_plain_goal(line_num, char_pos)
                        
                        if 'result' in response and response['result']:
                            result = response['result']
                            
                            # Display the proof state
                            if 'goals' in result and result['goals']:
                                print(f"\nPROOF STATE at column {char_pos}:")
                                for text in result['goals']:
                                    print(text)
                                found_context = True
                                break
                            elif isinstance(result, str) and result.strip():
                                print(f"\nPROOF STATE at column {char_pos}:")
                                print(result)
                                found_context = True
                                break
                    except Exception as e:
                        # Silently skip positions without proof state
                        pass
            
            if not found_context:
                print("\nNo proof state available")
        
        # Shutdown
        print("\n" + "=" * 80)
        print("Shutting down...")
        client.shutdown()
        
    except Exception as e:
        print(f"\nError: {e}")
        import traceback
        traceback.print_exc()
        if client.process:
            client.process.kill()
        sys.exit(1)


if __name__ == "__main__":
    main()