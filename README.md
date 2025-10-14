

Getting Started
--------------------------------------------------------------------------------

  - Install [Visual Studio Code] and its [Lean 4 extension].

    You should now have a new `lake` executable in your terminal.
    To test you installation so far, create a `hello-world` project:

    ```console
    $ lake new hello-world
    ```

    then into the newly created `hello-world` directory, 
    compile your `hello-world` application:

    ```console
    $ lake build
    info: hello-world: no previous manifest, creating one from scratch
    info: toolchain not updated; already up-to-date
    Build completed successfully (8 jobs).
    ```

    and run it:

    ```console
    $ lake exe hello-world
    Hello, world!
    ```

  - To work with the Lean & Python examples, install [uv] and [curl].

    Test your installation with

    ```console
    $ uv help
    An extremely fast Python package manager.

    Usage: uv [OPTIONS] <COMMAND>

    ...
    ```

    and on Linux or MacOS

    ```console
    $ curl --help
    Usage: curl [options...] <url>
    ...
    ```

    On Windows do instead:

    ```console
    $ curl.exe --help
    Usage: curl [options...] <url>
    ...
    ```

  - If you like fonts with [coding ligatures], have a look at [Fira Code] 
    (or [JetBrains Mono]). To install it, select it as the editor font and
    enable ligatures in Visual Studio Code, [follow these instructions].



[Visual Studio Code]: https://code.visualstudio.com/
[Lean 4 extension]: https://marketplace.visualstudio.com/items?itemName=leanprover.lean4
[uv]: https://docs.astral.sh/uv/
[Fira Code]: https://fonts.google.com/specimen/Fira+Code
[JetBrains Mono]: https://www.jetbrains.com/lp/mono/
[coding ligatures]: https://betterwebtype.com/5-free-monospaced-fonts-with-coding-ligatures/
[follow these instructions]: https://github.com/tonsky/FiraCode/wiki/VS-Code-Instructions