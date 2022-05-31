# ANSI color codes
class Color:
    COLOR_SEQ = "\033[1;%dm"
    ENDC = '\033[0m'
    BOLD = '\033[1m'
    UNDERLINE = '\033[4m'
    BLACK = '\033[30m'
    BLUE = '\033[34m'
    MAGENTA = '\033[35m'
    CYAN = '\033[36m'
    LIGHT_GRAY = '\033[37m'
    DEFAULT = '\033[39m'
    DARK_GRAY = '\033[90m'
    RED = '\033[91m'
    GREEN = '\033[92m'
    YELLOW = '\033[93m'
    BLUE = '\033[94m'
    LIGHT_MAGENTA = '\033[95m'


def err(string):
    print(Color.RED + '[x] ' + str(string) + Color.ENDC)


def warn(string):
    print(Color.YELLOW + '[-] ' + str(string) + Color.ENDC)


def success(string):
    print(Color.GREEN + '[@] ' + str(string) + Color.ENDC)


def info(string):
    print(Color.CYAN + '[#] ' + str(string) + Color.ENDC)


def debug(string):
    print(Color.DARK_GRAY + '[*] ' + str(string) + Color.ENDC)
