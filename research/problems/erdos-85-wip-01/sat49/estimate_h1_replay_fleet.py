#!/usr/bin/env python3
"""Planning sensitivities, not a measured fleet throughput forecast."""
import json
from math import ceil
from decimal import Decimal as D
rate = D('0.4284'); spot = D('0.1535'); disk = D(300)*D('0.08')/D(720); ip = D('0.005')
rows=[]
for count in (12019,13350):
 for n in (8,16,32):
  base=D(count)*D(984)/D(3600)
  h=base*D('1.25')+D(n)*D('0.5')
  spot_h=base*D('1.25')*D('1.10')+D(n)*D('0.5')
  rows.append({'jobs':count,'shards':n,'vcpus':8*n,'max_jobs_if_count_balanced':ceil(count/n),
   'compile_box_hours':float(base),'ideal_wall_days':float(base/D(n)/D(24)),
   'planned_box_hours':float(h),'planned_allocated_vcpu_hours':float(8*h),
   'planned_wall_days':float(h/D(n)/D(24)),
   'ondemand_compute_usd':float(h*rate),'gp3_usd':float(h*disk),'ipv4_usd':float(h*ip),
   'ondemand_infrastructure_usd':float(h*(rate+disk+ip)),
   'spot_sensitivity_infrastructure_usd':float(spot_h*(spot+disk+ip)),
   'spot_sensitivity_wall_days':float(spot_h/D(n)/D(24)),
   'double_compile_infrastructure_usd':float((2*base*D('1.25')+D(n)*D('0.5'))*(rate+disk+ip))})
print(json.dumps({'seconds_per_certificate':984,'noncompile_and_retry_factor':1.25,'bootstrap_hours_per_box':0.5,
 'gp3_gb_per_box':300,'gb_month_hours':720,'spot_additional_factor':1.10,'rows':rows},indent=2))
