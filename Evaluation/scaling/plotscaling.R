#!/usr/bin/env Rscript
library(tidyverse)
library(readr)
library(fs)
library(tikzDevice)

args = commandArgs(trailingOnly=TRUE)
if (length(args)<1) {
  stop("expected CSV file path. usage: plotscaling.R <csv-file-path>", call.=FALSE)
}

stats <- read_csv(args[1], col_types = cols(time = col_double()))
filter(stats, problemsize < 999999) %>%
transform(time = time*10) %>%
ggplot(mapping = aes(x=`problemsize`, y =`time`, color = `tool`, shape = `tool`))  +
  geom_col(mapping = aes(fill = `tool`), position=position_dodge2())  +
  xlab("problem size") +
  ylab("time [s $\\cdot 10^{-1}$] (log)") + 
  #geom_text(mapping = aes(x = `problemsize`, y = 0.3, label = ifelse(is.na(`time`), "X", "")), position=position_dodge2())
  #geom_point() +
  #geom_line() +
  scale_y_log10() +
  scale_x_continuous(breaks = stats$problemsize) +
  theme_light() +
  theme(legend.position = c(0.1,0.92),
        legend.title = element_blank(),
        panel.grid.major.x = element_blank(),
        panel.grid.minor.x = element_blank(),
        legend.background=element_blank())

ggsave(fs::path_ext_set(args[1], "pdf"))
ggsave(fs::path_ext_set(args[1], "png"))
