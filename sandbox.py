import random
import string

d : dict[str, int] = {"a": 1, "b": 2, "c": 3}

d["z"] = None

random_key : str = random.choice(string.ascii_letters)

d.get(random_key)