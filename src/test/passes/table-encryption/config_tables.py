# This file is distributed under the Apache License v2.0. See LICENSE for
# details.

import omvll
from functools import lru_cache

omvll.config.shuffle_functions = False
omvll.config.local_byte_array_sections = [".rodata.compound_string."]
omvll.config.encrypt_tables = [
    {
        "name": "gTestTable",
        "stride": 24,
        "seed": 0x12345678,
        "ring_section": ".sbss",
        "fields": [
            {"kind": "scalar", "offset": 0, "size": 1, "key": 0x11111111},
            {"kind": "scalar", "offset": 2, "size": 2, "key": 0x22222222},
            {"kind": "scalar", "offset": 4, "size": 4, "key": 0x33333333},
            {"kind": "inline_string", "offset": 8, "size": 8, "slots": 4, "key": 0x44444444},
            {
                "kind": "pointer_string",
                "offset": 16,
                "size": 32,
                "slots": 4,
                "key": 0x55555555,
                "extra_strings": ["gFallbackStr"],
            },
        ],
    }
]


class Config(omvll.ObfuscationConfig):
    def obfuscate_string(self, mod, func, string: bytes):
        return omvll.StringEncOptLocal()


@lru_cache(maxsize=1)
def omvll_get_config():
    return Config()
