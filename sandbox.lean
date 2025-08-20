import Python

def pythonCode := r#"
import requests

URL = "https://api.chucknorris.io/jokes/random"

def get_joke():
  joke_info = requests.get(URL).json()
  return joke_info["value"]
"#

def randomJoke : IO String := do
  Python.exec! pythonCode
  let joke <- Python.eval! "get_joke()"
  return joke

#eval do
  let joke <- randomJoke
  IO.println joke
