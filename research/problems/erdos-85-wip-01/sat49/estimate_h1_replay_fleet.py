#!/usr/bin/env python3
"""Planning sensitivities, not a measured fleet throughput forecast."""
import json
from math import ceil
from decimal import Decimal as D
rate = D('0.4284'); spot = D('0.1535'); disk = D(300)*D('0.08')/D(720); ip = D('0.005')
byte_factor = D(509000000)/D(346105417)
rows=[]
for count in (12019,13350):
 for n in (8,16,32):
  base=D(count)*D(984)/D(3600)
  h=base*D('1.25')+D(n)*D('0.5')
  spot_h=base*D('1.25')*D('1.10')+D(n)*D('0.5')
  byte_h=base*byte_factor*D('1.25')+D(n)*D('0.5')
  byte_spot_h=base*byte_factor*D('1.25')*D('1.10')+D(n)*D('0.5')
  rows.append({'jobs':count,'shards':n,'vcpus':8*n,'max_jobs_if_count_balanced':ceil(count/n),
   'compile_box_hours':float(base),'ideal_wall_days':float(base/D(n)/D(24)),
   'planned_box_hours':float(h),'planned_allocated_vcpu_hours':float(8*h),
   'planned_wall_days':float(h/D(n)/D(24)),
   'byte_weighted_compile_box_hours':float(base*byte_factor),
   'byte_weighted_planned_wall_days':float(byte_h/D(n)/D(24)),
   'byte_weighted_ondemand_infrastructure_usd':float(byte_h*(rate+disk+ip)),
   'byte_weighted_spot_infrastructure_usd':float(byte_spot_h*(spot+disk+ip)),
   'ondemand_compute_usd':float(h*rate),'gp3_usd':float(h*disk),'ipv4_usd':float(h*ip),
   'ondemand_infrastructure_usd':float(h*(rate+disk+ip)),
   'spot_sensitivity_infrastructure_usd':float(spot_h*(spot+disk+ip)),
   'spot_sensitivity_wall_days':float(spot_h/D(n)/D(24)),
   'double_compile_infrastructure_usd':float((2*base*D('1.25')+D(n)*D('0.5'))*(rate+disk+ip))})
print(json.dumps({'seconds_per_certificate':984,'reported_mean_gzip_bytes':509000000,'pilot_gzip_bytes':346105417,
 'byte_weight_factor':float(byte_factor),'ondemand_hourly_usd':float(rate),'spot_hourly_usd':float(spot),
 'gp3_gb_month_usd':0.08,'public_ipv4_hourly_usd':float(ip),'noncompile_and_retry_factor':1.25,'bootstrap_hours_per_box':0.5,
 'gp3_gb_per_box':300,'gb_month_hours':720,'spot_additional_factor':1.10,'rows':rows},indent=2))
