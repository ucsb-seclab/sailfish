import copy
import logging
from .globals import *
from .printer import *


LOGGER_COLORS = {
    'DEBUG': Color.DARK_GRAY,
    'INFO': Color.DARK_GRAY,
    'WARNING': Color.GREEN,
    'ERROR': Color.RED,
    'CRITICAL': Color.CYAN
}


class ColoredFormatter(logging.Formatter):
    def format(self, record):
        record = copy.copy(record)
        levelname = record.levelname
        if levelname in LOGGER_COLORS:
            levelname_color = Color.COLOR_SEQ % (30 + LOGGER_COLORS[levelname]) + levelname + Color.ENDC
            record.levelname = levelname_color
        return logging.Formatter.format(self, record)


# Initialize a logger that does not interfere with
# Celery family of loggers, especially the root logger
def init_logging(logger_name, log_file=None, file_mode='a', console=False):
    # Configure log format
    log_format_string = "[%(levelname)s] | %(asctime)s | %(name)-15s | %(message)s"
    date_fmt_string = DATE_FORMAT
    formatter = logging.Formatter(log_format_string, date_fmt_string)
    log = logging.getLogger(logger_name)
    log.setLevel(logging.INFO)
    # Turn off log message propagation all the way to the root logger.
    # If root logger is configured to have one or more handlers by
    # other modules, all log messages sent to our logger appears
    # those many times. Disabling root logger is not an elegant option,
    # because that turns off log messages (which might be important)
    # sent by other modules.
    log.propagate = False

    # Do *NOT* configure root logger will Celery.
    # Logs will be sent to console or wherever Celery
    # sends the logs by default
    # logging.basicConfig(filename=log_file, filemode=file_mode, format=log_format_string, datefmt=date_fmt_string, level=logging.INFO)

    # Configure and attach a file handler
    if log_file:
        file_handler = logging.FileHandler(log_file, mode=file_mode)
        file_handler.setLevel(logging.INFO)
        file_handler.setFormatter(formatter)
        log.addHandler(file_handler)

    # Configure and attach a console handler
    if console:
        console_handler = logging.StreamHandler()
        console_handler.setLevel(logging.INFO)
        # color_formatter = ColoredFormatter()
        console_handler.setFormatter(formatter)
        # console_handler.setFormatter(color_formatter)
        log.addHandler(console_handler)
    
    # import logging_tree; logging_tree.printout()
    return log


# We forgot to close the logger explicitly.
# Hundreds of file handles were left open from
# each of the analysis task. If <pid> is the PID
# of the pool worker, the open file handles can be
# listed using: "cat /proc/<pid>/fd". This is why
# the multiprocessing pool used to hang after some time
# Ref: https://stackoverflow.com/a/15474586
def del_logging(log):
    handlers = log.handlers[:]
    for handler in handlers:
        handler.flush()
        handler.close()
        log.removeHandler(handler)
    del(log)
