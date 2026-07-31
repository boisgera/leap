import Lean

/-!

> In a given programming language design, a *first-class citizen* is an entity
> which supports all the operations generally available to other entities.
> These operations typically include being passed as an argument,
> returned from a function, and assigned to a variable.

Source: [Wikipedia](https://en.wikipedia.org/wiki/First-class_citizen)
-/

/-!
> *Higher-order programming* is a style of computer programming that uses
> software components, like functions, modules or objects, as values.
> It is usually instantiated with, or borrowed from, models of computation
> such as lambda calculus which make heavy use of higher-order functions.
> A programming language can be considered higher-order if components,
> such as procedures or labels, can be used just like data. For example,
> these elements could be used in the same way as arguments or values.

Source: [Wikepedia](https://en.wikipedia.org/wiki/Higher-order_programming)
-/

/-
Use the GitHub Web API to display the number of stars of the Python repository.

`stars.py`:

```python
# /// script
# dependencies = ["requests"]
# ///
import requests
import time

PYTHON_GITHUB_URL = "https://api.github.com/repos/python/cpython"

def fetch_cpython_stars():
    response = requests.get(PYTHON_GITHUB_URL)
    r_json = response.json()
    return r_json["stargazers_count"]

print(f"⭐ {fetch_cpython_stars()}")
```

```console
$ uv run stars.py
⭐ 73982
```

Unfortunately, network requests can fail. But we can wait a bit and retry a few
times if happens, maybe the network will heal itself in the meantime?
To achieve this, we can do:

```python
def fetch_cpython_stars_with_retry(max_retries=3, delay=1.0):
    for attempt in range(max_retries):
        try:
            return fetch_cpython_stars()
        except Exception:
            if attempt < max_retries - 1:
                time.sleep(delay)
            else:
                raise

print(f"⭐ {fetch_cpython_stars_with_retry()}")
```

Wait! We actually have here a general tool: the "try again when it fails"
feature can be encapsulated in a `retry` function that does not hardcode
the core task:

```python
def retry(function, max_retries=3, delay=1.0):
    for attempt in range(max_retries):
        try:
            return function()
        except Exception:
            if attempt < max_retries - 1:
                time.sleep(delay)
            else:
                raise

print(f"⭐ {retry(fetch_cpython_stars)}")
```
Nice! That works because Python supports higher-order programming quite well:
we can use a function as a (higher-order) function arguments for example.
-/

/-!
The Lean version:
-/

/-!
⚠️ Install the CLI tool [curl](https://curl.se/) is first and check you can
call it in the terminal:

```
$  curl --version
curl 8.5.0 (x86_64-pc-linux-gnu) libcurl/8.5.0 OpenSSL/3.0.13 zlib/1.3 brotli/1.1.0 zstd/1.5.5 libidn2/2.3.7 libpsl/0.21.2 (+libidn2/2.3.7) libssh/0.10.6/openssl/zlib nghttp2/1.59.0 librtmp/2.3 OpenLDAP/2.6.10
Release-Date: 2023-12-06, security patched: 8.5.0-2ubuntu10.11
Protocols: dict file ftp ftps gopher gophers http https imap imaps ldap ldaps mqtt pop3 pop3s rtmp rtsp scp sftp smb smbs smtp smtps telnet tftp
Features: alt-svc AsynchDNS brotli GSS-API HSTS HTTP2 HTTPS-proxy IDN IPv6 Kerberos Largefile libz NTLM PSL SPNEGO SSL threadsafe TLS-SRP UnixSockets zstd
```
-/

def Http.get (url : String) : IO String := do
  let out ← IO.Process.output { cmd := "curl", args := #["--silent", url] }
  return out.stdout

def lean4Url := "https://api.github.com/repos/leanprover/lean4"

def fetch_lean_stars : IO Unit := do
  let jsonString ← Http.get lean4Url
  let json ← IO.ofExcept (Lean.Json.parse jsonString)
  let object ← IO.ofExcept json.getObj?
  let stargazersNumber : Lean.JsonNumber :=
    match object.get? "stargazers_count" with
    | some (Lean.Json.num n) => n
    | _ => panic! "wtf!"
  IO.println stargazersNumber

#eval fetch_lean_stars
-- 8638

partial def retry
    (action : IO Unit)
    (maxRetries : Nat := 3)
    (delayMs : UInt32 := 1000)
    : IO Unit := do
  try
    action
  catch e =>
    if maxRetries == 0 then
      throw e
    else
      IO.sleep delayMs
      retry action (maxRetries - 1) delayMs

#eval retry fetch_lean_stars
-- 8638
