#!/usr/bin/env Rscript
library(tidyverse)
library(readr)
library(fs)
library(RColorBrewer)
library(tikzDevice)

args = commandArgs(trailingOnly=TRUE)
if (length(args)<1) {
  stop("expected CSV file path. usage: plotscaling.R <csv-file-path>", call.=FALSE)
}

stats_raw <- read_csv(args[1], col_types = cols(time = col_double()))
# sort: ours first (for color scheme)

stats <- filter(stats_raw, problemsize < 999999) %>%
transform(time = time*10, tool=ifelse(tool=="lean-egg","eggxplosion", ifelse(tool == "coq", "coq-congruence", tool)))
stats$tool <- factor(stats$tool,levels=c("eggxplosion", "coq-congruence", "lean-simp"))

p <- ggplot(data =stats, mapping = aes(x=`problemsize`, y =`time`, fill = `tool`))  +
  geom_col(mapping = aes(fill = `tool`), position=position_dodge2())  +
  xlab("problem size") +
  ylab("time [$\\cdot 10^{-1} s$] (log)") +
  #geom_text(mapping = aes(x = `problemsize`, y = 0.3, label = ifelse(is.na(`time`), "X", "")), position=position_dodge2())
  #geom_point() +
  #geom_line() +
  scale_y_log10(expand=expansion(mult=c(0,0.1))) + # No space below the bars but 10% above them; https://ggplot2.tidyverse.org/reference/expansion.html
  scale_x_continuous(breaks = stats$problemsize) +
  scale_fill_brewer(palette="Set2")  +
  theme_light() +                                                    
  theme(legend.position = c(0.1,0.90),
        legend.title = element_blank(),
        panel.grid.major.x = element_blank(),
        panel.grid.minor.x = element_blank(),
        legend.background=element_blank())

tikz(file = fs::path_ext_set(args[1], "tex"), standAlone = F, width=10,height=4)
print(p)
dev.off()

p
ggsave(fs::path_ext_set(args[1], "png"))
#ggsave(fs::path_ext_set(args[1], "pdf"))

