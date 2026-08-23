
```lean4
import Lean
```

Redux: is some languages, there is a clear split between functions and data and
you can't do with data many things that you can with functions.

But this is not a fatality:

  - in some programming languages (untype lambda-calculus),
    the only object is function, the data stuff (numbers, lists, etc)
    is built on top. This is the conceptual founadtion of FP.
  - you don't have to be that extreme to qualify as a FP language,
    but functions should at least have equal rights. Question to ask:
    can you put you function in a list? Have a function be a function
    argument. Then it's fine!
  - First-class functions open the way to higher-order programming
    and constructors like filter, map and folds. For/while loops become
    not necessary, since recursion + FP can replace them!


The untyped lambda calculus in Python
--------------------------------------------------------------------------------

(Just natural numbers and succ ATM...)

The constraint: every object is a function that takes a function and returns
a function (**TODO** a bit more complex ; hard to explain without a reference
to Scott's construction?).


```python
def zero(f):
  def id(g):
    return g
  return id

def one(f):
  def apply_f(g):
    return f(g)
  return apply_f

def two(f):
  def apply_f_twice(g):
    return f(f(x))
  return apply_f_twice

def succ(n):
  def succ_n(f):
    def apply_f_n_plus_one_times(g):
      h = n(f)(g)  # f applied n times to g
      return f(h)  # f applied n + 1 times to g
  return succ_n
```


Equal rights for functions!
--------------------------------------------------------------------------------

> In a given programming language design, a *first-class citizen* is an entity
> which supports all the operations generally available to other entities.
> These operations typically include being passed as an argument,
> returned from a function, and assigned to a variable.

Source: [Wikipedia](https://en.wikipedia.org/wiki/First-class_citizen)

> *Higher-order programming* is a style of computer programming that uses
> software components, like functions, modules or objects, as values.
> It is usually instantiated with, or borrowed from, models of computation
> such as lambda calculus which make heavy use of higher-order functions.
> A programming language can be considered higher-order if components,
> such as procedures or labels, can be used just like data. For example,
> these elements could be used in the same way as arguments or values.

Source: [Wikipedia](https://en.wikipedia.org/wiki/Higher-order_programming)

```lean4
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
```

The Lean version:

⚠️ Install the CLI tool [curl](https://curl.se/) is first and check you can
call it in the terminal:

```
$  curl --version
curl 8.5.0 (x86_64-pc-linux-gnu) libcurl/8.5.0 OpenSSL/3.0.13 zlib/1.3 brotli/1.1.0 zstd/1.5.5 libidn2/2.3.7 libpsl/0.21.2 (+libidn2/2.3.7) libssh/0.10.6/openssl/zlib nghttp2/1.59.0 librtmp/2.3 OpenLDAP/2.6.10
Release-Date: 2023-12-06, security patched: 8.5.0-2ubuntu10.11
Protocols: dict file ftp ftps gopher gophers http https imap imaps ldap ldaps mqtt pop3 pop3s rtmp rtsp scp sftp smb smbs smtp smtps telnet tftp
Features: alt-svc AsynchDNS brotli GSS-API HSTS HTTP2 HTTPS-proxy IDN IPv6 Kerberos Largefile libz NTLM PSL SPNEGO SSL threadsafe TLS-SRP UnixSockets zstd
```

```lean4
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
```
