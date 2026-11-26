# This file is distributed under the Apache License v2.0. See LICENSE for
# details.

import omvll
from functools import lru_cache

omvll.config.local_byte_array_sections = [".rodata.game."]


class Config(omvll.ObfuscationConfig):
    def obfuscate_string(self, _, __, string: bytes):
        if string == b"\xbb\x00\xe8\xff" or string == b"\xbd\x00\xe5\xff":
            return omvll.StringEncOptLocal()
        if string == b"\xda\x00\xee\xff":
            return omvll.StringEncOptGlobal()
        return None


@lru_cache(maxsize=1)
def omvll_get_config():
    return Config()
