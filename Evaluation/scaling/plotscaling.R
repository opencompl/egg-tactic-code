library(tidyverse)
library(readr)
stats <- read_csv("stats.csv", col_types = cols(time = col_double()))
filter(stats, problemsize < 11) %>%
transform(time = time*10) %>%
ggplot(mapping = aes(x=`problemsize`, y =`time`, color = `tool`, shape = `tool`))  +
  geom_col(mapping = aes(fill = `tool`), position=position_dodge2())  +
  xlab("problem size") +
  ylab("time [s · 10⁻¹]") + 
  #geom_text(mapping = aes(x = `problemsize`, y = 0.3, label = ifelse(is.na(`time`), "X", "")), position=position_dodge2())
  #geom_point() +
  #geom_line() +
  scale_y_log10() 
ggsave("plotscaling.pdf")
